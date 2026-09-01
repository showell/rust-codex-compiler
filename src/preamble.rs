//! The IR chapter's PREAMBLE -- everything the compiler writes before `(defs`.
//!
//! ```text
//! (chapter "NegIntParse"
//!   (title "NegIntParse")
//!   (prose "")
//!   (pblocks)
//!   (anns)
//!   (sections "Construction" "Slicing" "Slicing(extended)" ... "Body")
//!   (ctors "MkTup2" "MkTup3" "MkTup4" "MkTup5")
//!   (eff-ops)
//!   (grounds)
//!   (type-defs
//!   (var-def "Tup2" (tparams "a" "b") (ctors (var-ctor "MkTup2" (fields ...)))))
//! ```
//!
//! **This is the only whole-corpus oracle that exists before the type
//! checker.** The `(defs` bodies below it carry a type on every node --
//! `(apply (name "f" (fn text int-default)) ... int-default)` -- so reaching
//! them needs scope, check and lower. Everything ABOVE `(defs` is fixed by
//! syntax alone, and it is present in all 1,012 gold IRs. Until this existed,
//! every claim about the parser's shape rested on unit tests written by
//! reading Cobblestone, and `parse.truth` -- one subject, declaration level.
//!
//! **It must be given a RESOLVED unit**, the thing `cite_resolve.resolve`
//! builds and the golds were cut from. A gold names sections from `Foreword
//! ListUtils` and constructors from `Foreword Tuple` that appear nowhere in
//! the program's own file. The ladder's `resolve_corpus.py` writes them.
//!
//! Six `a-` forms appear in a gold's type-defs and no others: `a-named`
//! (61,734 of them), `a-app`, `a-bounded` (4,893) and `a-fun` (19). No
//! effect row, no tuple, no `forall`. The emitter covers what is there and
//! answers `(a-unknown)` for the rest, which is upstream's own fallback and
//! is visible in a diff rather than silent.

use crate::charcode::CHAR_CODE;
use crate::cst::{Node, NodeKind};
use crate::token::Kind;

/// Order two names the way `text-compare` does, which is NOT alphabetical.
///
/// `ctor-names` is a `SkipListText` -- a SORTED skip list -- and
/// `skip-list-text-to-list` hands back its order. `text-compare` is a builtin
/// over `Text`, and **Codex `Text` is CCE**, so comparing bytes compares
/// CHAR-CODES: the frequency-ordered private alphabet, `etaoinshrdlcumwfgypbvkjxqz`
/// for lowercase and the same order shifted for uppercase. So `E` is 39, `N`
/// is 44, `M` is 52 and `J` is 61, and the compiler's own gold reads
/// `"EndOfFile" "EndKeyword" "ErrorToken" "ErrorTy" "ErrExpr" "ElseKeyword"`
/// -- En before Er before El, and `EndOfFile` before `EndKeyword` because `O`
/// is 42 and `K` is 60. Sorting these as ASCII gets every one of them wrong.
///
/// A byte at or above 128 is a CCE tier-1 lead, and every char-code is under
/// 97, so any such character sorts after every tier-0 one either way.
fn cce_key(s: &str) -> Vec<u8> {
    s.bytes()
        .map(|b| if (b as usize) < CHAR_CODE.len() { CHAR_CODE[b as usize] } else { b })
        .collect()
}

/// `ir-quote`: backslash, double quote and newline, and nothing else.
fn quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            _ => out.push(c),
        }
    }
    out.push('"');
    out
}

/// `is-letter-code c | is-digit-code c`, on a CHARACTER.
///
/// `join-title-parts` tests the last character written and the first arriving,
/// not the last and first BYTE. On ASCII the two readings agree and on nothing
/// else do they: a chapter section called
/// `Cyrillic (CCE 113-127->а о е и н т с р в л к м д п у)` keeps every one of
/// those spaces in the gold, because Cyrillic is a CCE tier-1 LETTER -- while
/// a byte test sees a UTF-8 continuation byte, calls it punctuation and joins
/// the letters into one word.
fn is_letter_or_digit(cp: u32) -> bool {
    (cp < 128 && (cp as u8 as char).is_ascii_alphanumeric()) || crate::lexer::is_tier1_letter(cp)
}

/// The first character of a byte slice, and the last, as codepoints.
fn first_cp(b: &[u8]) -> Option<u32> {
    (!b.is_empty()).then(|| crate::lexer::utf8_cp(b, 0))
}

fn last_cp(b: &[u8]) -> Option<u32> {
    // Walk back over continuation bytes to the lead of the final character.
    let mut i = b.len().checked_sub(1)?;
    while i > 0 && b[i] & 0xC0 == 0x80 {
        i -= 1;
    }
    Some(crate::lexer::utf8_cp(b, i))
}

/// The text after `Chapter:` / `Section:`, joined the way `join-title-parts`
/// joins it: a space goes in only when the last character already written and
/// the first character arriving are BOTH a letter or a digit. So `Section:
/// Slicing (extended)` is stored as `Slicing(extended)` -- the space before
/// `(` disappears because `(` is punctuation, and the one after it never
/// existed.
pub fn header_text(n: &Node, src: &[u8]) -> String {
    let mut acc: Vec<u8> = Vec::new();
    let mut past_colon = false;
    for t in n.tokens() {
        if t.kind == Kind::Colon && !past_colon {
            past_colon = true;
            continue;
        }
        if !past_colon || t.kind.is_trivia() || t.kind == Kind::Newline {
            continue;
        }
        let next = t.text(src);
        let (Some(last), Some(first)) = (last_cp(&acc), first_cp(next)) else {
            acc.extend_from_slice(next);
            continue;
        };
        if is_letter_or_digit(last) && is_letter_or_digit(first) {
            acc.push(b' ');
        }
        acc.extend_from_slice(next);
    }
    String::from_utf8_lossy(&acc).into_owned()
}

fn text_of(t: &crate::token::Token, src: &[u8]) -> String {
    String::from_utf8_lossy(t.text(src)).into_owned()
}

/// The first name-shaped token under a node -- for a TYPE's name, which is
/// always a TypeIdentifier and may sit behind a `mutable`.
fn first_name(n: &Node, src: &[u8]) -> Option<String> {
    n.tokens()
        .find(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier))
        .map(|t| text_of(t, src))
}

/// The first token a node holds, whatever KIND it is.
///
/// A record field's name may be a keyword -- `is-field-name-token` admits
/// `end`, and `span.end` is why -- so looking for an Identifier finds the
/// field's TYPE instead and names the field after it. The compiler's own
/// `SourceSpan` has a field called `end`, and the gold IR said
/// `(rec-field "end" ...)` where we said `(rec-field "SourcePosition" ...)`.
/// The parser puts the name first by construction, so take the first token.
fn leading_token(n: &Node, src: &[u8]) -> Option<String> {
    n.tokens().find(|t| !t.kind.is_trivia()).map(|t| text_of(t, src))
}

/// `desugar-type-expr`, as far as the forms a type definition can hold.
fn atype(n: &Node, src: &[u8]) -> String {
    let kids = n.child_nodes();
    match n.kind {
        NodeKind::NamedType => {
            let name = n
                .tokens()
                .filter(|t| !t.kind.is_trivia())
                .map(|t| text_of(t, src))
                .collect::<Vec<_>>()
                .concat();
            format!("(a-named {})", quote(&name))
        }
        // A parenthesised type is transparent: upstream has no node for it.
        NodeKind::ParenType => kids.first().map_or_else(unknown, |k| atype(k, src)),
        NodeKind::FunType => match kids.as_slice() {
            [p, r] => format!("(a-fun {} {})", atype(p, src), atype(r, src)),
            _ => unknown(),
        },
        // A type application is CURRIED: `Vector 4 Integer` is
        // `(a-app (a-app (a-named "Vector") (args (a-named "4"))) (args
        // (a-named "Integer")))`, one argument per node. Upstream builds it
        // that way an argument at a time -- `continue-type-args` wraps
        // `AppType base [arg]` and loops -- while our CST keeps the arguments
        // flat under one node, so the fold happens here.
        NodeKind::AppType => match kids.split_first() {
            Some((base, args)) => args.iter().fold(atype(base, src), |acc, a| {
                format!("(a-app {acc} (args {}))", atype(a, src))
            }),
            None => unknown(),
        },
        NodeKind::BoundedIntType => {
            let base = kids.first().map_or_else(unknown, |k| atype(k, src));
            // `Integer between -1 and 4294967295`: the minus is its own
            // token, and dropping it turned -1 into 1 in the compiler's own
            // `EffectRow.tail-id`. A minus is a SIGN here only when a number
            // follows it immediately.
            let toks: Vec<_> = n.tokens().filter(|t| !t.kind.is_trivia()).collect();
            let mut nums: Vec<String> = Vec::new();
            for (i, t) in toks.iter().enumerate() {
                if t.kind != Kind::IntegerLiteral {
                    continue;
                }
                let negated = i > 0 && toks[i - 1].kind == Kind::Minus;
                nums.push(format!("{}{}", if negated { "-" } else { "" }, text_of(t, src)));
            }
            let mode = n
                .tokens()
                .find_map(|t| match t.text(src) {
                    b"wrapping" => Some("ov-wrap"),
                    b"clamping" => Some("ov-clamp"),
                    _ => None,
                })
                .unwrap_or("ov-error");
            match nums.as_slice() {
                [lo, hi] => format!("(a-bounded {base} {lo} {hi} {mode})"),
                _ => unknown(),
            }
        }
        NodeKind::LinearType => {
            format!("(a-linear {})", kids.first().map_or_else(unknown, |k| atype(k, src)))
        }
        NodeKind::PropEqType => match kids.as_slice() {
            [l, r] => format!("(a-propeq {} {})", atype(l, src), atype(r, src)),
            _ => unknown(),
        },
        NodeKind::ForAllType => "(a-forall)".to_string(),
        // `(A, B)` is `TupN A B`, and the effect row and everything else is
        // not reachable from a type definition in this corpus.
        NodeKind::TupleType => {
            let n_elems = kids.len();
            let mut out = format!("(a-named \"Tup{n_elems}\")");
            for k in &kids {
                out = format!("(a-app {out} (args {}))", atype(k, src));
            }
            out
        }
        _ => unknown(),
    }
}

fn unknown() -> String {
    "(a-unknown)".to_string()
}

fn tparams(td: &Node, src: &[u8]) -> String {
    td.children_of(NodeKind::TypeParams)
        .flat_map(|p| p.tokens())
        .filter(|t| matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier))
        .map(|t| format!(" {}", quote(&text_of(t, src))))
        .collect()
}

fn type_def(td: &Node, src: &[u8]) -> Option<String> {
    let name = quote(&first_name(td, src)?);
    let tp = tparams(td, src);
    if let Some(rec) = td.children_of(NodeKind::RecordBody).next() {
        let fields: String = rec
            .children_of(NodeKind::RecordFieldDef)
            .map(|f| {
                let fname = leading_token(f, src).unwrap_or_default();
                let ty = f.child_nodes().first().map_or_else(unknown, |t| atype(t, src));
                format!(" (rec-field {} {ty})", quote(&fname))
            })
            .collect();
        let mutable = td
            .tokens()
            .any(|t| t.kind == Kind::MutableKeyword)
            .then_some(" (mutable)")
            .unwrap_or("");
        return Some(format!("(rec-def {name} (tparams{tp}) (fields{fields}){mutable})"));
    }
    if let Some(var) = td.children_of(NodeKind::VariantBody).next() {
        let ctors: String = var
            .children_of(NodeKind::VariantCtor)
            .map(|c| {
                let cname = leading_token(c, src).unwrap_or_default();
                let fields: String = c
                    .children_of(NodeKind::CtorField)
                    .map(|f| {
                        format!(
                            " {}",
                            f.child_nodes().first().map_or_else(unknown, |t| atype(t, src))
                        )
                    })
                    .collect();
                format!(" (var-ctor {} (fields{fields}))", quote(&cname))
            })
            .collect();
        return Some(format!("(var-def {name} (tparams{tp}) (ctors{ctors}))"));
    }
    if let Some(unit) = td.children_of(NodeKind::UnitBody).next() {
        let base = unit.child_nodes().first().map_or_else(unknown, |t| atype(t, src));
        return Some(format!("(unit-def {name} {base})"));
    }
    // `Energy = unit family Millijoule` is an ordinary unit definition over
    // Integer -- a unit family IS integer-backed, and its `Member = <factor>`
    // lines are conversion factors, not type definitions of their own.
    if td.children_of(NodeKind::UnitFamilyBody).next().is_some() {
        return Some(format!("(unit-def {name} (a-named \"Integer\"))"));
    }
    None
}

/// The chapter header, up to and including the `(defs` opener -- upstream's
/// `emit-ir-chapter-prefix`.
pub fn emit(tree: &Node, src: &[u8]) -> String {
    // The unit's own chapter is the LAST one: the resolver puts every cited
    // chapter first and the program itself last.
    let chapter = tree
        .descendants(NodeKind::ChapterHeader)
        .last()
        .map(|n| header_text(n, src))
        .unwrap_or_default();
    let sections: String = tree
        .descendants(NodeKind::SectionHeader)
        .iter()
        .map(|n| format!(" {}", quote(&header_text(n, src))))
        .collect();
    let type_defs = tree.descendants(NodeKind::TypeDef);
    // Every variant constructor, plus every UNIT type's own name --
    // `collect-ctor-names` inserts that too, which is easy to miss because a
    // unit type has no constructors of its own.
    let mut ctor_names: Vec<String> = type_defs
        .iter()
        .flat_map(|td| td.children_of(NodeKind::VariantBody))
        .flat_map(|v| v.children_of(NodeKind::VariantCtor))
        .filter_map(|c| leading_token(c, src))
        .collect();
    ctor_names.extend(
        type_defs
            .iter()
            .filter(|td| {
                td.children_of(NodeKind::UnitBody).next().is_some()
                    || td.children_of(NodeKind::UnitFamilyBody).next().is_some()
            })
            .filter_map(|td| first_name(td, src)),
    );
    // A sorted skip list: sorted by `text-compare`, and unique.
    ctor_names.sort_by(|a, b| cce_key(a).cmp(&cce_key(b)));
    ctor_names.dedup();
    let ctors: String = ctor_names.iter().map(|c| format!(" {}", quote(c))).collect();
    let tds: String = type_defs
        .iter()
        .filter_map(|td| type_def(td, src))
        .map(|t| format!("\n  {t}"))
        .collect();

    // `grounds Device.Port, Device.Block` publishes one entry per effect,
    // each `"<chapter>\n<effect>"` -- the chapter it was written in, which is
    // why this walks the document in order rather than collecting the
    // declarations on their own. A dotted effect is one name.
    let mut grounds: Vec<String> = Vec::new();
    let mut current_chapter = String::new();
    for child in tree.child_nodes() {
        match child.kind {
            NodeKind::ChapterHeader => current_chapter = header_text(child, src),
            NodeKind::Grounds => {
                let mut name = String::new();
                for t in child.tokens().filter(|t| !t.kind.is_trivia()) {
                    match t.kind {
                        Kind::GroundsKeyword | Kind::Newline | Kind::EndOfFile => {}
                        Kind::Comma => {
                            if !name.is_empty() {
                                grounds.push(format!("{current_chapter}\n{name}"));
                                name.clear();
                            }
                        }
                        _ => name.push_str(&text_of(t, src)),
                    }
                }
                if !name.is_empty() {
                    grounds.push(format!("{current_chapter}\n{name}"));
                }
            }
            _ => {}
        }
    }
    let grounds: String = grounds.iter().map(|g| format!(" {}", quote(g))).collect();

    // Source order, not the sorted order `ctors` uses: the gold reads
    // `(eff-ops "print-line-uni" "read-line")` and char-code order would put
    // `read-line` first, since `r` is 21 and `p` is 31.
    let eff_ops: String = tree
        .descendants(NodeKind::EffectDef)
        .iter()
        .flat_map(|e| e.children_of(NodeKind::EffectOp))
        .filter_map(|o| leading_token(o, src))
        .map(|o| format!(" {}", quote(&o)))
        .collect();

    let q = quote(&chapter);
    format!(
        "(chapter {q}\n  (title {q})\n  (prose \"\")\n  (pblocks)\n  (anns)\n  \
(sections{sections})\n  (ctors{ctors})\n  (eff-ops{eff_ops})\n  (grounds{grounds})\n  \
(type-defs{tds})\n  (defs"
    )
}
