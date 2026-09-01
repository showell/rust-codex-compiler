//! The pattern grammar. Cobblestone's `Pat` has six variants and this is all
//! of them -- `Parser.codex`, Section: Pattern Parsing.
//!
//! Three rules a reasonable guess gets backwards, each one costing a fix:
//!
//! **A constructor's fields are PARENTHESIZED, one paren group each.** It is
//! `is Cons (h) (t)`, never `is Cons h t`. Juxtaposition is how an
//! APPLICATION is written and patterns are not applications, so a ctor
//! followed by a bare name is a ctor with no fields, and the name is left for
//! whatever comes next to choke on.
//!
//! **`(x)` is not a tuple and not a wrapper.** Upstream returns the inner
//! pattern itself when no comma follows, so only a comma builds a `TuplePat`.
//! We keep a `ParenPat` node because the tree is lossless and the parentheses
//! have to live somewhere -- exactly as `Paren` does for expressions -- and
//! the AST reads through it.
//!
//! **`Vector [a, b]` is its own form**, recognised by the constructor's TEXT
//! being `Vector` and the next token being `[`. Nothing else in the language
//! puts a bracket after a constructor in pattern position.
//!
//! Upstream never fails: every branch consumes a token, and anything
//! unrecognised becomes a `WildPat`. We keep that shape but split the
//! catch-all out as [`NodeKind::ErrPat`], because a wildcard the author wrote
//! and a token we did not understand are not the same fact, and folding them
//! together would make the second one uncountable. The desugarer treats both
//! as a wildcard.

use crate::cst::NodeKind;
use crate::parser::Parser;
use crate::token::Kind;

/// Upstream's `is-literal`, shared with the expression grammar.
fn is_literal(k: Kind) -> bool {
    matches!(
        k,
        Kind::IntegerLiteral
            | Kind::NumberLiteral
            | Kind::TextLiteral
            | Kind::CharLiteral
            | Kind::TrueKeyword
            | Kind::FalseKeyword
    )
}

/// Upstream's `is-reserved-keyword`. A keyword in a binding position is taken
/// as the name anyway and reported, so that one mistake yields one diagnostic
/// rather than a cascade of them.
pub(crate) fn is_reserved_keyword(k: Kind) -> bool {
    matches!(
        k,
        Kind::LetKeyword
            | Kind::InKeyword
            | Kind::BetweenKeyword
            | Kind::IfKeyword
            | Kind::IsKeyword
            | Kind::OtherwiseKeyword
            | Kind::ThenKeyword
            | Kind::ElseKeyword
            | Kind::WhenKeyword
            | Kind::WhereKeyword
            | Kind::SuchThatKeyword
            | Kind::ActKeyword
            | Kind::EndKeyword
            | Kind::RecordKeyword
            | Kind::CitesKeyword
            | Kind::GroundsKeyword
            | Kind::ClaimKeyword
            | Kind::ProofKeyword
            | Kind::QedKeyword
            | Kind::InductionKeyword
            | Kind::ForAllKeyword
            | Kind::ThereExistsKeyword
            | Kind::LinearKeyword
            | Kind::MutableKeyword
            | Kind::PunctualKeyword
            | Kind::UnitKeyword
            | Kind::LazyKeyword
            | Kind::EffectKeyword
            | Kind::WithKeyword
            | Kind::RevisedKeyword
            | Kind::TrueKeyword
            | Kind::FalseKeyword
            | Kind::ClassKeyword
            | Kind::InstanceKeyword
    )
}

pub(crate) fn parse_pattern(p: &mut Parser<'_>) -> NodeKind {
    let cp = p.b.checkpoint();
    let Some(t) = p.sig(0) else {
        p.b.start(NodeKind::ErrPat);
        p.b.end();
        return NodeKind::ErrPat;
    };
    let kind = match t.kind {
        // `otherwise` is the wildcard the language spells out. `_` reaches
        // upstream's catch-all and lands on the same node, so it is written
        // here rather than left to ours -- it is a wildcard the author MEANT.
        Kind::OtherwiseKeyword | Kind::Underscore => {
            p.bump();
            NodeKind::WildPat
        }
        k if is_literal(k) => {
            p.bump();
            NodeKind::LitPat
        }
        Kind::TypeIdentifier => {
            let is_vector = p.text_is(t, b"Vector");
            p.bump();
            return ctor_fields(p, cp, is_vector);
        }
        Kind::Identifier => {
            p.bump();
            NodeKind::VarPat
        }
        k if is_reserved_keyword(k) => {
            p.err(format!(
                "'{}' is a reserved keyword and cannot be used as a pattern variable; rename it",
                String::from_utf8_lossy(t.text(p.src))
            ));
            p.bump();
            NodeKind::VarPat
        }
        Kind::LeftParen => {
            p.bump();
            return paren_or_tuple(p, cp);
        }
        _ => {
            p.bump();
            NodeKind::ErrPat
        }
    };
    p.b.wrap_from(cp, kind);
    kind
}

/// `Cons (h) (t)`, `Red`, and `Vector [a, b]`. The bracket form is tested on
/// every round, exactly as upstream does, so it is reached whether or not
/// paren fields came first.
fn ctor_fields(p: &mut Parser<'_>, cp: usize, is_vector: bool) -> NodeKind {
    loop {
        if is_vector && p.kind(0) == Some(Kind::LeftBracket) {
            p.bump();
            vec_elems(p);
            p.b.wrap_from(cp, NodeKind::VecPat);
            return NodeKind::VecPat;
        }
        if p.kind(0) != Some(Kind::LeftParen) {
            break;
        }
        p.bump();
        parse_pattern(p);
        if p.kind(0) == Some(Kind::RightParen) {
            p.bump();
        } else {
            p.err("expected ')' closing a constructor field");
        }
    }
    p.b.wrap_from(cp, NodeKind::CtorPat);
    NodeKind::CtorPat
}

fn vec_elems(p: &mut Parser<'_>) {
    if p.kind(0) == Some(Kind::RightBracket) {
        p.bump();
        return;
    }
    loop {
        parse_pattern(p);
        if p.kind(0) == Some(Kind::Comma) {
            p.bump();
            continue;
        }
        if p.kind(0) == Some(Kind::RightBracket) {
            p.bump();
        } else {
            p.err("expected ']' closing a vector pattern");
        }
        return;
    }
}

/// The `(` is already eaten. A comma makes a tuple; without one this is the
/// inner pattern wearing parentheses.
pub(crate) fn paren_or_tuple(p: &mut Parser<'_>, cp: usize) -> NodeKind {
    parse_pattern(p);
    let mut commas = 0;
    while p.kind(0) == Some(Kind::Comma) {
        commas += 1;
        p.bump();
        parse_pattern(p);
    }
    if p.kind(0) == Some(Kind::RightParen) {
        p.bump();
    } else {
        p.err("expected ')' closing a pattern");
    }
    let kind = if commas > 0 { NodeKind::TuplePat } else { NodeKind::ParenPat };
    p.b.wrap_from(cp, kind);
    kind
}

#[cfg(test)]
mod tests {
    use crate::cst::NodeKind;
    use crate::parser::parse;

    /// The shape of the first match arm in `when e is <arm>`.
    fn arm(arm_src: &str) -> String {
        let src =
            format!("Chapter: T\n\nSection: S\n  f : A\n  f (x) =\n   when e\n    is {arm_src}\n");
        let p = parse(src.as_bytes());
        let lexed = crate::lexer::tokenize(src.as_bytes());
        let in_tree: Vec<_> = p.tree.tokens().copied().collect();
        assert_eq!(in_tree, lexed.tokens, "a token did not reach the tree");
        assert_eq!(p.unparsed_bodies, 0, "body not understood: {arm_src}");
        p.tree.descendants(NodeKind::MatchArm).first().expect("an arm").shape()
    }

    #[test]
    fn a_constructors_fields_are_parenthesised_one_group_each() {
        assert_eq!(arm("Cons (h) (t) -> h"), "(MatchArm (CtorPat (VarPat) (VarPat)) (Name))");
        assert_eq!(arm("Red -> 1"), "(MatchArm (CtorPat) (Lit))");
    }

    #[test]
    fn juxtaposition_is_not_a_constructor_field() {
        // `is Cons h t` is a ctor with NO fields followed by two stray names.
        // Patterns are not applications, and reading them as one would accept
        // a program the compiler rejects.
        let src = "Chapter: T\n\nSection: S\n  f : A\n  f (x) =\n   when e\n    is Cons h t -> h\n";
        let p = parse(src.as_bytes());
        let a = p.tree.descendants(NodeKind::MatchArm);
        // The stray names become the arm's BODY, and the missing arrow is
        // reported -- which is how the mistake reaches the author.
        assert_eq!(
            a.first().map(|n| n.shape()).unwrap_or_default(),
            "(MatchArm (CtorPat) (App (Name) (Name)))"
        );
        assert!(!p.errors.is_empty(), "the stray names must be reported");
    }

    #[test]
    fn only_a_comma_makes_a_tuple() {
        assert_eq!(arm("(x) -> x"), "(MatchArm (ParenPat (VarPat)) (Name))");
        assert_eq!(arm("(a, b) -> a"), "(MatchArm (TuplePat (VarPat) (VarPat)) (Name))");
    }

    #[test]
    fn patterns_nest_through_parentheses() {
        assert_eq!(
            arm("Just (Just (x)) -> x"),
            "(MatchArm (CtorPat (CtorPat (VarPat))) (Name))"
        );
    }

    #[test]
    fn a_bracket_after_vector_is_a_vector_pattern() {
        // Recognised by the constructor's TEXT. `Other [a]` is not one.
        assert_eq!(
            arm("Vector [a, b] -> a"),
            "(MatchArm (VecPat (VarPat) (VarPat)) (Name))"
        );
    }

    #[test]
    fn otherwise_and_underscore_are_both_wildcards() {
        assert_eq!(arm("otherwise -> 1"), "(MatchArm (WildPat) (Lit))");
        assert_eq!(arm("_ -> 1"), "(MatchArm (WildPat) (Lit))");
    }

    #[test]
    fn a_literal_pattern_is_not_a_variable() {
        assert_eq!(arm("0 -> 1"), "(MatchArm (LitPat) (Lit))");
        assert_eq!(arm("'a' -> 1"), "(MatchArm (LitPat) (Lit))");
        assert_eq!(arm("True -> 1"), "(MatchArm (LitPat) (Lit))");
    }

    #[test]
    fn a_pipe_gives_one_arm_several_patterns() {
        // Upstream fans these out into one arm per pattern sharing a body. A
        // lossless tree cannot duplicate the body, so the fanning is the
        // desugarer's and the arm keeps all three patterns.
        assert_eq!(
            arm("Red | Orange | Yellow -> 1"),
            "(MatchArm (CtorPat) (CtorPat) (CtorPat) (Lit))"
        );
    }

    #[test]
    fn when_after_a_pattern_is_a_guard() {
        // Reading to the arrow and calling the lot a pattern swallows the
        // guard whole -- which is what the token-bag placeholder did.
        assert_eq!(
            arm("Num (n) when n < 0 -> 1"),
            "(MatchArm (CtorPat (VarPat)) (Guard (Bin (Name) (Lit))) (Lit))"
        );
    }
}
