//! Type definitions: `Name a b = <body>`, and the four bodies a `=` can lead
//! to -- `Parser.codex`, Section: Type Definition Parsing.
//!
//! ```text
//! Pair (a) = record { fst : a, snd : a }
//! Step (a) = | One (a) (Iter a) | Done
//! Colour   = Red | Green | Blue  deriving Show, Eq
//! Length   = unit family Millimeter
//! ```
//!
//! **A variant does not need its leading pipe.** `Colour = Red | Green` is a
//! variant and `Alias = Integer` is not, and the only thing separating them is
//! whether a pipe turns up before the end of the line -- upstream scans ahead
//! for exactly that (`looks-like-variant`). Requiring the pipe reads the first
//! constructor of every unpiped variant as an alias.
//!
//! **A record field name may be a keyword.** It is `is-field-name-token`, the
//! same set field access uses, so `end : Integer` is an ordinary field.
//!
//! **`unit family` is not a type**, it is a list of `Member = <factor>` lines,
//! and it is told from the plain `unit T` form by the word `family` -- an
//! ordinary identifier, not a keyword.
//!
//! The comma between record fields and between `deriving` names is OPTIONAL,
//! the same way it is between `let` bindings.

use crate::cst::NodeKind;
use crate::parser::{starts_an_item, starts_conversion, Parser};
use crate::token::{Kind, Token};

/// `(a)` and `(A)` are type parameters; `(a, b)` and `(f x)` are not.
fn is_paren_type_param(p: &Parser<'_>) -> bool {
    p.kind(0) == Some(Kind::LeftParen)
        && matches!(p.kind(1), Some(Kind::Identifier) | Some(Kind::TypeIdentifier))
        && p.kind(2) == Some(Kind::RightParen)
}

/// Upstream's `is-type-param-pattern`, used by the document layer to tell a
/// type definition from a value definition before committing to either.
pub(crate) fn starts_type_params(p: &Parser<'_>, n: usize) -> bool {
    p.kind(n) == Some(Kind::Identifier)
        || (p.kind(n) == Some(Kind::LeftParen)
            && matches!(p.kind(n + 1), Some(Kind::Identifier) | Some(Kind::TypeIdentifier))
            && p.kind(n + 2) == Some(Kind::RightParen))
}

pub(crate) fn parse_type_def(p: &mut Parser<'_>, first: Token) {
    p.b.start(NodeKind::TypeDef);
    if p.kind(0) == Some(Kind::MutableKeyword) {
        p.bump();
    }
    p.bump(); // the name; the document layer has already checked it is one
    type_params(p);
    if p.kind(0) == Some(Kind::Equals) {
        p.bump();
        p.skip_newlines();
        body(p);
        deriving(p);
    } else {
        p.err("expected '=' in a type definition");
    }
    trailer(p, first.col);
    p.b.end();
}

/// What sits between the end of the body and the next top-level item.
///
/// Prose is the common case and is not a defect: a chapter explains its types
/// in indented paragraphs, and the lexer has already turned the column-2 line
/// into trivia while leaving its continuation lines as ordinary tokens.
/// Everything else is a body the grammar did not finish, and it is kept under
/// a name that says so and COUNTED -- a half-read type definition must not
/// pass for a whole one.
fn trailer(p: &mut Parser<'_>, col: u32) {
    loop {
        let Some(t) = p.sig(0) else { return };
        if t.kind == Kind::EndOfFile
            || (t.col <= col && (starts_an_item(t.kind) || starts_conversion(p)))
        {
            return;
        }
        // A blank line belongs to no construct. Counting one as an unread body
        // reported every `deriving` clause in the checkout as a defect, since
        // it is the one body form that does not end by skipping newlines.
        if t.kind == Kind::Newline {
            p.bump();
            continue;
        }
        if crate::parser::in_prose_block(p) {
            crate::parser::eat_prose_block(p);
            continue;
        }
        let tcp = p.b.checkpoint();
        p.bump();
        while let Some(t) = p.sig(0) {
            if t.kind == Kind::EndOfFile
                || (t.col <= col && (starts_an_item(t.kind) || starts_conversion(p)))
                || crate::parser::in_prose_block(p)
            {
                break;
            }
            p.bump();
        }
        p.unread_type_defs += 1;
        p.b.wrap_from(tcp, NodeKind::Error);
    }
}

fn type_params(p: &mut Parser<'_>) {
    let cp = p.b.checkpoint();
    let mut n = 0;
    loop {
        if is_paren_type_param(p) {
            p.bump();
            p.bump();
            p.bump();
        } else if p.kind(0) == Some(Kind::Identifier) {
            p.bump();
        } else {
            break;
        }
        n += 1;
    }
    if n > 0 {
        p.b.wrap_from(cp, NodeKind::TypeParams);
    }
}

fn body(p: &mut Parser<'_>) {
    match p.kind(0) {
        Some(Kind::RecordKeyword) => record_body(p),
        Some(Kind::UnitKeyword) => unit_body(p),
        Some(Kind::Pipe) => variant_body(p),
        Some(Kind::TypeIdentifier) if looks_like_variant(p) => variant_body(p),
        _ => {
            // Upstream answers `None` here and hands the whole definition
            // back. There is no such thing in a tree that must cover its
            // tokens, so the trailer takes them and the count says so.
        }
    }
}

/// Is there a pipe before the end of this line? That, and only that, is what
/// makes `Colour = Red | Green` a variant rather than an alias.
fn looks_like_variant(p: &Parser<'_>) -> bool {
    let mut n = 1;
    loop {
        match p.kind(n) {
            Some(Kind::Pipe) => return true,
            Some(Kind::Newline) | Some(Kind::EndOfFile) | None => return false,
            _ => n += 1,
        }
    }
}

fn record_body(p: &mut Parser<'_>) {
    let cp = p.b.checkpoint();
    p.bump(); // record
    if p.kind(0) == Some(Kind::LeftBrace) {
        p.bump();
    } else {
        p.err("expected '{' after 'record'");
    }
    p.skip_newlines();
    loop {
        if p.kind(0) == Some(Kind::RightBrace) {
            p.bump();
            break;
        }
        if !p.kind(0).is_some_and(crate::expr::is_field_name) {
            break;
        }
        let fcp = p.b.checkpoint();
        p.bump(); // the field name
        if p.kind(0) == Some(Kind::Colon) {
            p.bump();
        } else {
            p.err("expected ':' in a record field");
        }
        crate::types::parse_type(p);
        p.b.wrap_from(fcp, NodeKind::RecordFieldDef);
        p.skip_newlines();
        if p.kind(0) == Some(Kind::Comma) {
            p.bump();
            p.skip_newlines();
        }
    }
    p.b.wrap_from(cp, NodeKind::RecordBody);
}

fn variant_body(p: &mut Parser<'_>) {
    let cp = p.b.checkpoint();
    if p.kind(0) == Some(Kind::TypeIdentifier) {
        ctor(p);
    }
    while p.kind(0) == Some(Kind::Pipe) {
        p.bump();
        p.skip_newlines();
        ctor(p);
    }
    p.b.wrap_from(cp, NodeKind::VariantBody);
}

fn ctor(p: &mut Parser<'_>) {
    let cp = p.b.checkpoint();
    p.bump(); // the constructor's name
    while p.kind(0) == Some(Kind::LeftParen) {
        let fcp = p.b.checkpoint();
        p.bump();
        crate::types::parse_type(p);
        if p.kind(0) == Some(Kind::RightParen) {
            p.bump();
        } else {
            p.err("expected ')' closing a constructor field");
        }
        p.b.wrap_from(fcp, NodeKind::CtorField);
    }
    // The newlines go whether or not a return type follows, which is what lets
    // the constructors of a variant sit one per line.
    p.skip_newlines();
    if p.kind(0) == Some(Kind::Colon) {
        let rcp = p.b.checkpoint();
        p.bump();
        crate::types::parse_type(p);
        p.b.wrap_from(rcp, NodeKind::CtorReturn);
        p.skip_newlines();
    }
    p.b.wrap_from(cp, NodeKind::VariantCtor);
}

fn unit_body(p: &mut Parser<'_>) {
    let cp = p.b.checkpoint();
    p.bump(); // unit
    if !p.sig(0).is_some_and(|t| p.text_is(t, b"family")) {
        crate::types::parse_type(p);
        p.b.wrap_from(cp, NodeKind::UnitBody);
        return;
    }
    p.bump(); // family
    if p.kind(0) == Some(Kind::TypeIdentifier) {
        p.bump(); // the base unit
    } else {
        p.err("expected the base unit after 'unit family'");
    }
    p.skip_newlines();
    // `Member = <factor>` and nothing else. The three-token test is upstream's
    // rule written forwards: it looks, decides and only then consumes, where
    // upstream consumes and rewinds.
    while p.kind(0) == Some(Kind::TypeIdentifier)
        && p.kind(1) == Some(Kind::Equals)
        && p.kind(2) == Some(Kind::IntegerLiteral)
    {
        let mcp = p.b.checkpoint();
        p.bump();
        p.bump();
        p.bump();
        p.b.wrap_from(mcp, NodeKind::UnitFamilyMember);
        p.skip_newlines();
    }
    p.b.wrap_from(cp, NodeKind::UnitFamilyBody);
}

/// `deriving Show, Eq, Ord`, on the body's line or its own. `deriving` is an
/// ordinary identifier, so only its TEXT tells it from a definition's name.
fn deriving(p: &mut Parser<'_>) {
    p.skip_newlines();
    if !p.sig(0).is_some_and(|t| t.kind == Kind::Identifier && p.text_is(t, b"deriving")) {
        return;
    }
    let cp = p.b.checkpoint();
    p.bump();
    p.skip_newlines();
    while p.kind(0) == Some(Kind::TypeIdentifier) {
        p.bump();
        if p.kind(0) == Some(Kind::Comma) {
            p.bump();
            p.skip_newlines();
        } else {
            break;
        }
    }
    p.b.wrap_from(cp, NodeKind::Deriving);
}

#[cfg(test)]
mod tests {
    use crate::cst::NodeKind;
    use crate::parser::parse;

    /// The shape of the first type definition in a chapter.
    fn td(src_body: &str) -> String {
        let src = format!("Chapter: T\n\nSection: S\n  {src_body}\n");
        let p = parse(src.as_bytes());
        let lexed = crate::lexer::tokenize(src.as_bytes());
        let in_tree: Vec<_> = p.tree.tokens().copied().collect();
        assert_eq!(in_tree, lexed.tokens, "a token did not reach the tree");
        assert_eq!(p.unread_type_defs, 0, "body not understood: {src_body}");
        assert!(p.errors.is_empty(), "{:?} for {src_body}", p.errors);
        p.tree.descendants(NodeKind::TypeDef).first().expect("a type definition").shape()
    }

    #[test]
    fn a_record_body_is_one_node_per_field() {
        assert_eq!(
            td("Pair (a) = record { fst : a, snd : a }"),
            "(TypeDef (TypeParams) (RecordBody (RecordFieldDef (NamedType)) (RecordFieldDef (NamedType))))"
        );
    }

    #[test]
    fn a_record_field_name_may_be_a_keyword() {
        // `is-field-name-token` admits `end`, and `span.end` is why.
        assert_eq!(
            td("Span = record { end : Integer }"),
            "(TypeDef (RecordBody (RecordFieldDef (NamedType))))"
        );
    }

    #[test]
    fn the_comma_between_record_fields_is_optional() {
        assert_eq!(
            td("R = record {\n   a : Integer\n   b : Integer\n  }"),
            "(TypeDef (RecordBody (RecordFieldDef (NamedType)) (RecordFieldDef (NamedType))))"
        );
    }

    #[test]
    fn a_variant_does_not_need_its_leading_pipe() {
        // `Colour = Red | Green` is a variant and `Alias = Integer` is not.
        // The only difference is a pipe before the end of the line, which is
        // what upstream scans ahead for.
        let piped = td("Colour =\n   | Red\n   | Green");
        let bare = td("Colour = Red | Green");
        assert_eq!(piped, "(TypeDef (VariantBody (VariantCtor) (VariantCtor)))");
        assert_eq!(bare, piped);
    }

    #[test]
    fn a_constructors_fields_are_parenthesised_types() {
        assert_eq!(
            td("Step (a) = | One (a) (Iter a) | Done"),
            "(TypeDef (TypeParams) (VariantBody \
(VariantCtor (CtorField (NamedType)) (CtorField (AppType (NamedType) (NamedType)))) (VariantCtor)))"
        );
    }

    #[test]
    fn deriving_names_hang_off_the_definition() {
        assert_eq!(
            td("Colour = | Red | Green  deriving Show, Eq, Ord"),
            "(TypeDef (VariantBody (VariantCtor) (VariantCtor)) (Deriving))"
        );
    }

    #[test]
    fn a_unit_family_is_a_list_of_members_not_a_type() {
        // `unit family` and `unit T` differ by one word, and that word is an
        // ordinary identifier rather than a keyword.
        assert_eq!(
            td("Length = unit family Millimeter\n   Metre = 1000\n   Km = 1000000"),
            "(TypeDef (UnitFamilyBody (UnitFamilyMember) (UnitFamilyMember)))"
        );
        assert_eq!(td("Mass = unit Integer"), "(TypeDef (UnitBody (NamedType)))");
    }

    #[test]
    fn a_capitalised_name_with_paren_params_is_a_type_definition() {
        // Missing the paren form of a type parameter is silent: the whole
        // thing parses as a VALUE definition whose name happens to be
        // capitalised, and 26 in the checkout did exactly that.
        let src = "Chapter: T\n\nSection: S\n  Iter (a) = record { at : a }\n";
        let p = parse(src.as_bytes());
        assert_eq!(p.tree.descendants(NodeKind::TypeDef).len(), 1);
        assert_eq!(p.tree.descendants(NodeKind::Def).len(), 0);
    }

    #[test]
    fn a_mutable_record_is_still_a_type_definition() {
        assert_eq!(
            td("mutable S = record { at : Integer }"),
            "(TypeDef (RecordBody (RecordFieldDef (NamedType))))"
        );
    }
}
