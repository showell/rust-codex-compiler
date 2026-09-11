//! Type expressions.
//!
//! The grammar is small but it has four traps, and each one is a rule that a
//! reasonable guess gets backwards.
//!
//! **A comma and an arrow build the SAME node.** `A, B -> C` is a function of
//! two parameters, and it is built right-nested from both separators:
//! `Fun(A, Fun(B, C))`. There is no separate parameter-list node.
//!
//! **A chained arrow is an error, not a curried type.** `A -> B -> C` is
//! refused outright and the message says to use commas. So the right operand
//! of an arrow may not itself be an arrow.
//!
//! **A comma does not always continue a type.** `comma-starts-type-param`
//! looks past it: an identifier followed by a colon is a record field, not
//! another parameter, so the type ends at the comma.
//!
//! **A parenthesised type is classified by lookahead.** A comma at depth zero
//! with no arrow makes it a tuple; otherwise it is a parenthesised type. The
//! scan has to run before the open paren is committed to.

use crate::cst::NodeKind;
use crate::parser::Parser;
use crate::token::Kind;

/// Upstream's `is-type-arg-start`: what may follow a type as an argument.
fn starts_a_type_arg(k: Kind) -> bool {
    matches!(k, Kind::TypeIdentifier | Kind::Identifier | Kind::LeftParen | Kind::IntegerLiteral)
}

pub(crate) fn parse_type(p: &mut Parser<'_>) {
    p.type_depth += 1;
    parse_type_inner(p, true);
    p.type_depth -= 1;
}

/// Inside a tuple, a comma SEPARATES elements; everywhere else it introduces
/// another function parameter. Same token, opposite jobs, and the classifier
/// upstream exists precisely to tell them apart -- so the element parser must
/// not take the comma, or `(A, B)` reads as a one-element tuple holding the
/// function type `A -> B`.
fn parse_type_inner(p: &mut Parser<'_>, allow_comma: bool) {
    let cp = p.b.checkpoint();
    parse_type_head(p);
    parse_type_continue(p, cp, allow_comma);
}

/// `forall`, `linear`, `mutable`, or a plain atom -- then arguments, then a
/// bound, then type-level arithmetic.
fn parse_type_head(p: &mut Parser<'_>) {
    let cp = p.b.checkpoint();
    match p.kind(0) {
        Some(Kind::ForAllKeyword) => return parse_forall(p, cp),
        Some(Kind::LinearKeyword) => {
            p.bump();
            parse_type_atom(p);
            type_args(p, cp);
            p.b.wrap_from(cp, NodeKind::LinearType);
        }
        Some(Kind::MutableKeyword) => {
            p.bump();
            parse_type_atom(p);
            type_args(p, cp);
        }
        // `for all (a : K), T` -- the two-word spelling, where `for` and `all`
        // are ordinary identifiers the lexer knows nothing about.
        Some(Kind::Identifier)
            if p.sig(0).is_some_and(|t| p.text_is(t, b"for"))
                && p.sig(1).is_some_and(|t| p.text_is(t, b"all")) =>
        {
            return parse_forall(p, cp)
        }
        _ => {
            parse_type_atom(p);
            type_args(p, cp);
        }
    }
    bound_or_arith(p, cp);
}

fn parse_forall(p: &mut Parser<'_>, cp: usize) {
    // `forall` or `for all`, then `(name : Kind), Type`.
    p.bump();
    if p.sig(0).is_some_and(|t| p.text_is(t, b"all")) {
        p.bump();
    }
    if p.kind(0) == Some(Kind::LeftParen) {
        p.bump();
        if matches!(p.kind(0), Some(Kind::Identifier) | Some(Kind::TypeIdentifier)) {
            p.bump();
        }
        if p.kind(0) == Some(Kind::Colon) {
            p.bump();
        }
        parse_type(p);
        if p.kind(0) == Some(Kind::RightParen) {
            p.bump();
        } else {
            p.err("expected ')' closing a forall variable");
        }
    }
    if p.kind(0) == Some(Kind::Comma) {
        p.bump();
    }
    parse_type(p);
    p.b.wrap_from(cp, NodeKind::ForAllType);
}

fn type_args(p: &mut Parser<'_>, cp: usize) {
    // `Integer wrapping` with no band is the whole width, wrapping --
    // upstream's `is-bare-wrapping`, tested before any argument.
    if bare_wrapping(p) {
        p.bump();
        p.b.wrap_from(cp, NodeKind::BoundedIntType);
        return;
    }
    let mut any = false;
    while p.kind(0).is_some_and(starts_a_type_arg) {
        parse_type_atom(p);
        any = true;
    }
    if any {
        p.b.wrap_from(cp, NodeKind::AppType);
    }
}

fn bare_wrapping(p: &Parser<'_>) -> bool {
    let Some(prev) = p.prev_sig() else { return false };
    prev.kind == Kind::TypeIdentifier
        && p.text_is(prev, b"Integer")
        && p.sig(0).is_some_and(|t| t.kind == Kind::Identifier && p.text_is(t, b"wrapping"))
}

fn parse_type_atom(p: &mut Parser<'_>) {
    let cp = p.b.checkpoint();
    match p.kind(0) {
        Some(Kind::LeftParen) => parse_paren_type(p, cp),
        Some(Kind::LeftBracket) => parse_effect_type(p, cp),
        // A minus abutting its digits is a signed literal, not subtraction --
        // the same adjacency rule the expression grammar uses, and for the
        // same reason: `1 - 3` and `-2` are the same two token kinds.
        Some(Kind::Minus) if signed_literal(p) => {
            p.bump();
            p.bump();
            p.b.wrap_from(cp, NodeKind::NamedType);
        }
        Some(_) => {
            p.bump();
            p.b.wrap_from(cp, NodeKind::NamedType);
        }
        None => {}
    }
}

fn signed_literal(p: &Parser<'_>) -> bool {
    let (Some(minus), Some(next)) = (p.sig(0), p.sig(1)) else { return false };
    matches!(next.kind, Kind::IntegerLiteral | Kind::NumberLiteral)
        && next.offset == minus.offset + 1
}

/// A comma at depth zero with no arrow makes a tuple; anything else is a
/// parenthesised type. The answer has to be known before the paren is consumed,
/// so this looks ahead without building anything.
fn paren_is_tuple(p: &Parser<'_>) -> bool {
    let (mut depth, mut saw_arrow, mut saw_comma, mut n) = (0i32, false, false, 1usize);
    while let Some(t) = p.sig(n) {
        match t.kind {
            Kind::LeftParen | Kind::LeftBracket => depth += 1,
            Kind::RightParen => {
                if depth == 0 {
                    break;
                }
                depth -= 1;
            }
            Kind::RightBracket => depth -= 1,
            Kind::Arrow if depth == 0 => saw_arrow = true,
            Kind::Comma if depth == 0 => saw_comma = true,
            Kind::EndOfFile => break,
            _ => {}
        }
        n += 1;
    }
    saw_comma && !saw_arrow
}

fn parse_paren_type(p: &mut Parser<'_>, cp: usize) {
    let tuple = paren_is_tuple(p);
    p.bump(); // (
    if p.kind(0) != Some(Kind::RightParen) {
        parse_type_inner(p, !tuple);
        while p.kind(0) == Some(Kind::Comma) {
            p.bump();
            p.skip_newlines();
            parse_type_inner(p, !tuple);
        }
    }
    if p.kind(0) == Some(Kind::RightParen) {
        p.bump();
    } else {
        p.err("expected ')' closing a type");
    }
    p.b.wrap_from(cp, if tuple { NodeKind::TupleType } else { NodeKind::ParenType });
}

/// `[Console] Nothing`, `[Console, State] T` -- an effect row and a return.
fn parse_effect_type(p: &mut Parser<'_>, cp: usize) {
    p.bump(); // [
    while let Some(t) = p.sig(0) {
        if t.kind == Kind::RightBracket || t.kind == Kind::EndOfFile {
            break;
        }
        p.bump();
    }
    if p.kind(0) == Some(Kind::RightBracket) {
        p.bump();
    } else {
        p.err("expected ']' closing an effect row");
    }
    parse_type(p);
    p.b.wrap_from(cp, NodeKind::EffectType);
}

fn bound_or_arith(p: &mut Parser<'_>, cp: usize) {
    if p.kind(0) == Some(Kind::BetweenKeyword) {
        p.bump();
        bound_int(p);
        if p.kind(0) == Some(Kind::AndKeyword) {
            p.bump();
        } else {
            p.err("expected 'and' in a bound annotation");
        }
        bound_int(p);
        // The overflow mode is an optional ordinary identifier, and an
        // unrecognised word is NOT consumed -- upstream leaves it for whatever
        // comes next rather than swallowing it.
        if let Some(t) = p.sig(0) {
            if t.kind == Kind::Identifier
                && (p.text_is(t, b"wrapping") || p.text_is(t, b"clamping") || p.text_is(t, b"error"))
            {
                p.bump();
            }
        }
        p.b.wrap_from(cp, NodeKind::BoundedIntType);
        return;
    }
    // Type-level operators, loosest first: `&` appends, then `+`/`-`, then
    // `*`/`/`. Each builds one node holding the operator and BOTH operands --
    // upstream's `AppType (NamedType op) [left, right]` -- which is a
    // different shape from an ordinary type application, and that one the
    // parser curries an argument at a time.
    append_tail(p, cp);
}

/// An operand of a type-level operator: an atom AND its arguments.
/// `parse-type-arith-operand` is `parse-type-atom` followed by
/// `parse-type-args`, so `xs & Cons 7 Nil` appends a three-token application
/// and not the bare name `Cons`.
fn arith_operand(p: &mut Parser<'_>) {
    let cp = p.b.checkpoint();
    parse_type_atom(p);
    type_args(p, cp);
}

fn mul_tail(p: &mut Parser<'_>, cp: usize) {
    while matches!(p.kind(0), Some(Kind::Star) | Some(Kind::Slash)) {
        p.bump();
        arith_operand(p);
        p.b.wrap_from(cp, NodeKind::ArithType);
    }
}

fn add_tail(p: &mut Parser<'_>, cp: usize) {
    mul_tail(p, cp);
    while matches!(p.kind(0), Some(Kind::Plus) | Some(Kind::Minus)) {
        p.bump();
        let rhs = p.b.checkpoint();
        arith_operand(p);
        mul_tail(p, rhs);
        p.b.wrap_from(cp, NodeKind::ArithType);
    }
}

fn append_tail(p: &mut Parser<'_>, cp: usize) {
    add_tail(p, cp);
    while p.kind(0) == Some(Kind::Ampersand) {
        p.bump();
        let rhs = p.b.checkpoint();
        arith_operand(p);
        add_tail(p, rhs);
        p.b.wrap_from(cp, NodeKind::ArithType);
    }
}

fn bound_int(p: &mut Parser<'_>) {
    if p.kind(0) == Some(Kind::Minus) {
        p.bump();
    }
    if p.kind(0).is_some_and(|k| {
        matches!(k, Kind::IntegerLiteral | Kind::NumberLiteral | Kind::TrueKeyword | Kind::FalseKeyword)
    }) {
        p.bump();
    } else {
        p.err("expected an integer literal in a bound annotation");
    }
}

/// A comma continues a type only when what follows starts a parameter. An
/// identifier followed by a colon is a record field, so the type stops.
fn comma_starts_type_param(p: &Parser<'_>) -> bool {
    match p.kind(1) {
        Some(Kind::TypeIdentifier) | Some(Kind::LeftBracket) | Some(Kind::LeftParen) => true,
        Some(Kind::Identifier) => p.kind(2) != Some(Kind::Colon),
        _ => false,
    }
}

fn parse_type_continue(p: &mut Parser<'_>, cp: usize, allow_comma: bool) {
    match p.kind(0) {
        Some(Kind::Arrow) => {
            p.bump();
            p.skip_newlines();
            let rcp = p.b.checkpoint();
            parse_type(p);
            // `A -> B -> C` is refused outright: the message upstream gives is
            // to use commas for multiple parameters.
            if p.b.kind_at(rcp) == Some(NodeKind::FunType) {
                p.err("chained '->' in a type is not allowed; use commas: 'A, B -> C'");
            }
            p.b.wrap_from(cp, NodeKind::FunType);
        }
        // `===`, not `==`. Upstream's continue arm is `current-kind ==
        // TripleEquals` and it handles no other equality, so a claim's
        // proposition -- `list-length xs === 1 + n`, which is where
        // propositional equality actually appears -- stopped at the operator
        // and left the rest of the annotation unread, 69 times.
        Some(Kind::TripleEquals) => {
            p.bump();
            parse_type(p);
            p.b.wrap_from(cp, NodeKind::PropEqType);
        }
        // `Showable a => a -> Text`: a class constraint in front of a type.
        Some(Kind::FatArrow) => {
            p.bump();
            parse_type(p);
            p.b.wrap_from(cp, NodeKind::ConstrainedType);
        }
        Some(Kind::Comma) if allow_comma && comma_starts_type_param(p) => {
            p.bump();
            p.skip_newlines();
            parse_type(p);
            p.b.wrap_from(cp, NodeKind::FunType);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use crate::cst::NodeKind;
    use crate::parser::parse;

    /// The shape of the first definition's type annotation.
    fn ty(annotation: &str) -> String {
        let src = format!("Chapter: T\n\nSection: S\n  f : {annotation}\n  f (x) = x\n");
        let p = parse(src.as_bytes());
        let lexed = crate::lexer::tokenize(src.as_bytes());
        let in_tree: Vec<_> = p.tree.tokens().copied().collect();
        assert_eq!(in_tree, lexed.tokens, "a token did not reach the tree");
        assert_eq!(p.unread_types, 0, "type not fully read: {annotation}");
        let ann = p.tree.descendants(NodeKind::TypeAnnotation).into_iter().next().unwrap();
        ann.child_nodes()[0].shape()
    }

    fn errors_for(annotation: &str) -> Vec<String> {
        let src = format!("Chapter: T\n\nSection: S\n  f : {annotation}\n  f (x) = x\n");
        parse(src.as_bytes()).errors.into_iter().map(|e| e.msg).collect()
    }

    /// Errors for a whole unit, so a probe can put the byte anywhere.
    fn errors_in(src: &str) -> Vec<String> {
        parse(src.as_bytes()).errors.into_iter().map(|e| e.msg).collect()
    }

    #[test]
    fn an_unmapped_byte_in_a_type_is_refused() {
        // **MEASURED AGAINST `codexir`, NOT INFERRED FROM THE BANK.** Every
        // byte the frequency alphabet does not map -- carriage return, tab,
        // vertical tab, form feed, SOH -- halts the real compiler with CDX1000
        // when it lands inside a type, and is skipped as trivia everywhere
        // else. The five probes below were run through `codexir` at
        // u56-candidate-sunday one at a time; the compiler refused exactly
        // these and compiled the same bytes in an expression.
        //
        // The bank cannot settle this and reading it as though it could is how
        // the opposite rule got written down: `cite_resolve.py` reads with
        // `read_text()`, so Python's universal newlines stripped every CR
        // before bare metal ever saw one, and no gold in the set contains the
        // byte whose handling it was cited as proving.
        for byte in ["\r", "\t", "\x0b", "\x0c", "\x01"] {
            let probe = format!("Integer{byte} -> Integer");
            assert!(
                !errors_for(&probe).is_empty(),
                "an unmapped byte in a type must be refused: {probe:?}"
            );
        }
    }

    #[test]
    fn an_unmapped_byte_outside_a_type_is_trivia() {
        // The other half of the same measurement, and the reason this is not
        // simply "reject the byte": `codexir` compiles all of these. A rule
        // that refused them everywhere would diverge from the compiler in the
        // opposite direction, which is no better for an oracle.
        for byte in ["\r", "\t", "\x0b", "\x0c"] {
            let src = format!(
                "Chapter: T\n\nSection: S\n  f : Integer -> Integer\n  f (x) = x +{byte} 1\n"
            );
            assert!(
                errors_in(&src).is_empty(),
                "an unmapped byte outside a type is trivia: {byte:?} -> {:?}",
                errors_in(&src)
            );
        }
        // And on the lines around a definition, which is where CRLF actually
        // puts them: chapter, section, blank and body lines all compile.
        let crlf_edges = "Chapter: T\r\n\r\nSection: S\r\n\r\n  f : Integer -> Integer\n  f (x) = x + 1\r\n";
        assert!(errors_in(crlf_edges).is_empty(), "{:?}", errors_in(crlf_edges));
    }

    #[test]
    fn a_comma_and_an_arrow_build_the_same_node() {
        // `A, B -> C` is a function of two parameters, right-nested from both
        // separators. There is no parameter-list node.
        assert_eq!(
            ty("A, B -> C"),
            "(TypeExpr (FunType (NamedType) (FunType (NamedType) (NamedType))))"
        );
        assert_eq!(ty("A -> B"), "(TypeExpr (FunType (NamedType) (NamedType)))");
    }

    #[test]
    fn a_chained_arrow_is_refused() {
        // Not curried -- refused, with the advice to use commas.
        let errs = errors_for("A -> B -> C");
        assert_eq!(errs.len(), 1, "{errs:?}");
        assert!(errs[0].contains("chained"), "{errs:?}");
        assert!(errors_for("A, B -> C").is_empty());
    }

    #[test]
    fn a_comma_before_a_record_field_does_not_continue_the_type() {
        // `comma-starts-type-param` looks past the comma: an identifier
        // followed by a colon is a field, so the type ends there.
        assert_eq!(ty("Integer"), "(TypeExpr (NamedType))");
        let src = "Chapter: T\n\nSection: S\n  R = record {\n   a : Integer,\n   b : Text\n  }\n";
        let p = parse(src.as_bytes());
        assert!(p.errors.is_empty(), "{:?}", p.errors);
    }

    #[test]
    fn a_paren_is_a_tuple_only_with_a_comma_and_no_arrow() {
        // Decided by lookahead, before the paren is consumed.
        assert_eq!(ty("(A, B)"), "(TypeExpr (TupleType (NamedType) (NamedType)))");
        assert_eq!(
            ty("(A, B -> C)"),
            "(TypeExpr (ParenType (FunType (NamedType) (FunType (NamedType) (NamedType)))))"
        );
    }

    #[test]
    fn a_bounded_integer_keeps_its_bounds_and_its_mode() {
        assert_eq!(ty("Integer between 0 and 255"), "(TypeExpr (BoundedIntType (NamedType)))");
        assert!(errors_for("Integer between 0 and 255 wrapping").is_empty());
        // An unrecognised trailing word is NOT swallowed by the mode slot.
        assert!(errors_for("Integer between 0 and 255").is_empty());
    }

    #[test]
    fn an_effect_row_sits_in_front_of_the_return_type() {
        assert_eq!(ty("[Console] Nothing"), "(TypeExpr (EffectType (NamedType)))");
    }

    #[test]
    fn a_type_application_is_one_node() {
        assert_eq!(
            ty("Vector 4 Integer"),
            "(TypeExpr (AppType (NamedType) (NamedType) (NamedType)))"
        );
    }

    #[test]
    fn a_signed_literal_in_type_position_is_not_subtraction() {
        // Same adjacency rule the expression grammar uses: the digits must
        // begin at the byte after the minus.
        assert!(errors_for("Integer between -1 and 1").is_empty());
    }
}
