//! The expression grammar: a Pratt parser over the same lossless tree.
//!
//! Three things here are Codex-specific and none of them are optional.
//!
//! **A column floor.** Every definition body is parsed with the equation
//! name's column as `min_col`, and the binary loop stops at any token at or
//! left of it. That is what ends one definition and starts the next, in a
//! language with no layout tokens.
//!
//! **Newlines are significant outside brackets.** `paren_depth` decides
//! whether the parser may cross a line break. Outside brackets it may not,
//! which is why Codex refuses a multi-line application (CDX1070) instead of
//! silently reading the next line as an argument.
//!
//! **A minus that touches its operand is a negation.** `f a -2` and `f a - 2`
//! carry identical token KINDS; only the byte offsets separate an argument
//! from a subtraction. The lexer has already resolved `a-2` and `a-` into
//! single identifiers, so they never reach this test.

use crate::cst::NodeKind;
use crate::parser::Parser;
use crate::token::Kind;

/// Upstream's `operator-precedence`. The numbers are internal; the ORDER is
/// the contract, and `xor` sitting between `or` and `and` is the conventional
/// reading a reader assumes rather than checks.
fn precedence(k: Kind) -> i32 {
    match k {
        Kind::Caret => 9,
        Kind::Star | Kind::Slash => 8,
        Kind::Plus | Kind::Minus => 7,
        Kind::ColonColon => 6,
        Kind::DoubleEquals
        | Kind::NotEquals
        | Kind::LessThan
        | Kind::GreaterThan
        | Kind::LessOrEqual
        | Kind::GreaterOrEqual
        | Kind::TripleEquals
        | Kind::Tilde
        | Kind::TildeZero => 5,
        Kind::Ampersand | Kind::AndKeyword => 4,
        Kind::XorKeyword => 3,
        Kind::Pipe | Kind::OrKeyword => 2,
        Kind::PipeForward => 1,
        _ => -1,
    }
}

fn right_assoc(k: Kind) -> bool {
    matches!(k, Kind::ColonColon | Kind::Caret | Kind::Arrow)
}

/// What may begin an argument in an application.
fn starts_an_argument(k: Kind) -> bool {
    matches!(
        k,
        Kind::Identifier
            | Kind::TypeIdentifier
            | Kind::IntegerLiteral
            | Kind::NumberLiteral
            | Kind::TextLiteral
            | Kind::CharLiteral
            | Kind::TrueKeyword
            | Kind::FalseKeyword
            | Kind::LeftParen
            | Kind::LeftBracket
            | Kind::ActKeyword
            | Kind::WithKeyword
            | Kind::LazyKeyword
    )
}

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

/// The forms that end an application. Upstream's `is-compound`: once the
/// function position holds one of these, only field access may follow.
fn is_compound(kind: NodeKind) -> bool {
    matches!(
        kind,
        NodeKind::MatchExpr
            | NodeKind::IfExpr
            | NodeKind::LetExpr
            | NodeKind::ActBlock
            | NodeKind::FieldAssign
            | NodeKind::Lambda
            | NodeKind::ForExpr
    )
}

/// `not` takes a whole comparison and minus does not, which is upstream's
/// deliberate asymmetry: `-x + y` is `(-x) + y` because negation belongs to
/// the value it sits on, while `not a == b` is `not (a == b)` because the
/// other reading type-checks perfectly and is never what anybody meant.
const PREC_COMPARISON: i32 = 5;

pub(crate) fn parse_expr_col(p: &mut Parser<'_>, min_col: u32) -> NodeKind {
    parse_binary(p, 0, min_col)
}

pub(crate) fn parse_expr(p: &mut Parser<'_>) -> NodeKind {
    parse_binary(p, 0, 0)
}

fn parse_binary(p: &mut Parser<'_>, min_prec: i32, min_col: u32) -> NodeKind {
    let cp = p.b.checkpoint();
    let mut kind = parse_unary(p, min_col);
    loop {
        // A newline does not end a binary expression -- `a\n + b` continues --
        // but the column floor still applies to whatever follows it.
        let save = p.at();
        p.skip_newlines();
        let Some(t) = p.sig(0) else {
            let _ = save;
            return kind;
        };
        if min_col > 0 && t.col > 0 && t.col <= min_col {
            return kind;
        }
        let prec = precedence(t.kind);
        if prec < min_prec {
            return kind;
        }
        p.bump(); // the operator
        p.skip_newlines();
        let next_min = if right_assoc(t.kind) { prec } else { prec + 1 };
        parse_binary(p, next_min, min_col);
        p.b.wrap_from(cp, NodeKind::Bin);
        kind = NodeKind::Bin;
    }
}

fn parse_unary(p: &mut Parser<'_>, min_col: u32) -> NodeKind {
    let cp = p.b.checkpoint();
    match p.kind(0) {
        Some(Kind::Minus) => {
            p.bump();
            parse_unary(p, min_col);
            p.b.wrap_from(cp, NodeKind::Unary);
            NodeKind::Unary
        }
        Some(Kind::NotKeyword) => {
            p.bump();
            parse_binary(p, PREC_COMPARISON, min_col);
            p.b.wrap_from(cp, NodeKind::Unary);
            NodeKind::Unary
        }
        _ => parse_application(p),
    }
}

fn parse_application(p: &mut Parser<'_>) -> NodeKind {
    let cp = p.b.checkpoint();
    let mut kind = parse_atom(p);
    loop {
        if is_compound(kind) {
            // Only field access may follow a compound form.
            return parse_field_access(p, cp, kind);
        }
        if p.done() {
            return kind;
        }
        if p.paren_depth > 0 {
            p.skip_newlines();
        }
        let Some(t) = p.sig(0) else { return kind };

        if starts_an_argument(t.kind) {
            parse_atom(p);
            p.b.wrap_from(cp, NodeKind::App);
            kind = NodeKind::App;
            continue;
        }
        // A negated argument wraps ONE atom. Handing the minus to the unary
        // parser would read a whole application after it, so `f a -b c` would
        // come out as `f a (-(b c))` and quietly lose an argument.
        if t.kind == Kind::Minus && is_abutted_negation(p) {
            let ncp = p.b.checkpoint();
            p.bump();
            parse_atom(p);
            p.b.wrap_from(ncp, NodeKind::Unary);
            p.b.wrap_from(cp, NodeKind::App);
            kind = NodeKind::App;
            continue;
        }
        return parse_field_access(p, cp, kind);
    }
}

/// A minus abuts its operand when the next token starts at the very next byte.
fn is_abutted_negation(p: &Parser<'_>) -> bool {
    let (Some(minus), Some(next)) = (p.sig(0), p.sig(1)) else { return false };
    starts_an_argument(next.kind) && next.offset == minus.offset + 1
}

/// Upstream's `is-field-name-token`. A field name may be a keyword -- `span.end`
/// and `.record` are real -- but it may NOT be a TypeIdentifier, so the set is
/// neither "any identifier" nor "any word".
fn is_field_name(k: Kind) -> bool {
    matches!(
        k,
        Kind::Identifier
            | Kind::ActKeyword
            | Kind::EndKeyword
            | Kind::QedKeyword
            | Kind::EffectKeyword
            | Kind::WhereKeyword
            | Kind::WithKeyword
            | Kind::LinearKeyword
            | Kind::ClaimKeyword
            | Kind::ProofKeyword
            | Kind::RecordKeyword
            | Kind::ClassKeyword
            | Kind::InstanceKeyword
    )
}

fn parse_field_access(p: &mut Parser<'_>, cp: usize, mut kind: NodeKind) -> NodeKind {
    loop {
        match p.kind(0) {
            Some(Kind::Dot) => {
                p.bump();
                if p.kind(0).is_some_and(is_field_name) {
                    p.bump();
                    if p.kind(0) == Some(Kind::Equals) {
                        p.bump();
                        parse_expr(p);
                        p.b.wrap_from(cp, NodeKind::FieldAssign);
                        return NodeKind::FieldAssign;
                    }
                    p.b.wrap_from(cp, NodeKind::FieldAccess);
                    kind = NodeKind::FieldAccess;
                } else {
                    return kind;
                }
            }
            Some(Kind::RevisedKeyword) => {
                p.bump();
                p.skip_newlines();
                record_braces(p);
                p.b.wrap_from(cp, NodeKind::Revised);
                kind = NodeKind::Revised;
            }
            _ => return kind,
        }
    }
}

fn parse_atom(p: &mut Parser<'_>) -> NodeKind {
    let cp = p.b.checkpoint();
    let Some(t) = p.sig(0) else { return NodeKind::ErrExpr };
    match t.kind {
        k if is_literal(k) => {
            p.bump();
            p.b.wrap_from(cp, NodeKind::Lit);
            NodeKind::Lit
        }
        Kind::Identifier => {
            // `for` is a keyword the lexer does not know about: it arrives as
            // an ordinary identifier and only the parser separates it.
            if p.sig(0).is_some_and(|t| p.text_is(t, b"for")) {
                return parse_for(p, cp);
            }
            p.bump();
            p.b.wrap_from(cp, NodeKind::Name);
            parse_field_access(p, cp, NodeKind::Name)
        }
        Kind::TypeIdentifier => {
            p.bump();
            // `Name { field = .. }` is a record literal; a bare one is a name.
            if p.kind(0) == Some(Kind::LeftBrace) {
                record_braces(p);
                p.b.wrap_from(cp, NodeKind::RecordLit);
                return NodeKind::RecordLit;
            }
            p.b.wrap_from(cp, NodeKind::Name);
            parse_field_access(p, cp, NodeKind::Name)
        }
        Kind::LeftParen => parse_paren(p, cp),
        Kind::LeftBracket => parse_list(p, cp),
        Kind::IfKeyword => parse_if(p, cp),
        Kind::LetKeyword => parse_let(p, cp),
        Kind::WhenKeyword => parse_match(p, cp, NodeKind::MatchExpr),
        Kind::InductionKeyword => parse_match(p, cp, NodeKind::Induction),
        Kind::ActKeyword => parse_act(p, cp, NodeKind::ActBlock),
        Kind::TryingKeyword => parse_act(p, cp, NodeKind::TryExpr),
        Kind::WithKeyword => parse_act(p, cp, NodeKind::HandleExpr),
        Kind::WithTimeoutKeyword => parse_act(p, cp, NodeKind::WithTimeout),
        Kind::Backslash => parse_lambda(p, cp),
        Kind::LazyKeyword => {
            p.bump();
            parse_expr(p);
            p.b.wrap_from(cp, NodeKind::LazyExpr);
            NodeKind::LazyExpr
        }
        Kind::Dot => {
            // A leading `.field` selector.
            p.bump();
            if p.kind(0).is_some_and(is_field_name) {
                p.bump();
            }
            p.b.wrap_from(cp, NodeKind::Selector);
            NodeKind::Selector
        }
        _ => {
            p.bump();
            p.b.wrap_from(cp, NodeKind::ErrExpr);
            NodeKind::ErrExpr
        }
    }
}

fn parse_paren(p: &mut Parser<'_>, cp: usize) -> NodeKind {
    p.bump(); // (
    p.paren_depth += 1;
    p.skip_newlines();
    let mut commas = 0;
    if p.kind(0) != Some(Kind::RightParen) {
        parse_expr(p);
        p.skip_newlines();
        while p.kind(0) == Some(Kind::Comma) {
            commas += 1;
            p.bump();
            p.skip_newlines();
            parse_expr(p);
            p.skip_newlines();
        }
    }
    p.paren_depth -= 1;
    if p.kind(0) == Some(Kind::RightParen) {
        p.bump();
    } else {
        p.err("expected ')'");
    }
    let kind = if commas > 0 { NodeKind::Tuple } else { NodeKind::Paren };
    p.b.wrap_from(cp, kind);
    parse_field_access(p, cp, kind)
}

fn parse_list(p: &mut Parser<'_>, cp: usize) -> NodeKind {
    p.bump(); // [
    p.paren_depth += 1;
    p.skip_newlines();
    if p.kind(0) != Some(Kind::RightBracket) {
        parse_expr(p);
        p.skip_newlines();
        while p.kind(0) == Some(Kind::Comma) {
            p.bump();
            p.skip_newlines();
            parse_expr(p);
            p.skip_newlines();
        }
    }
    p.paren_depth -= 1;
    if p.kind(0) == Some(Kind::RightBracket) {
        p.bump();
    } else {
        p.err("expected ']'");
    }
    p.b.wrap_from(cp, NodeKind::ListLit);
    parse_field_access(p, cp, NodeKind::ListLit)
}

/// `{ field = expr, .. }`, shared by record literals and `revised`.
fn record_braces(p: &mut Parser<'_>) {
    if p.kind(0) != Some(Kind::LeftBrace) {
        p.err("expected '{'");
        return;
    }
    p.bump();
    p.paren_depth += 1;
    p.skip_newlines();
    while let Some(t) = p.sig(0) {
        if t.kind == Kind::RightBrace || t.kind == Kind::EndOfFile {
            break;
        }
        let fcp = p.b.checkpoint();
        p.bump(); // the field name
        if p.kind(0) == Some(Kind::Equals) {
            p.bump();
            p.skip_newlines();
            parse_expr(p);
        }
        p.b.wrap_from(fcp, NodeKind::RecordField);
        p.skip_newlines();
        if p.kind(0) == Some(Kind::Comma) {
            p.bump();
            p.skip_newlines();
        }
    }
    p.paren_depth -= 1;
    if p.kind(0) == Some(Kind::RightBrace) {
        p.bump();
    } else {
        p.err("expected '}'");
    }
}

fn parse_if(p: &mut Parser<'_>, cp: usize) -> NodeKind {
    p.bump(); // if
    parse_expr(p);
    p.skip_newlines();
    if p.kind(0) == Some(Kind::ThenKeyword) {
        p.bump();
    } else {
        p.err("expected 'then'");
    }
    p.skip_newlines();
    parse_expr(p);
    p.skip_newlines();
    if p.kind(0) == Some(Kind::ElseKeyword) {
        p.bump();
        p.skip_newlines();
        parse_expr(p);
    } else {
        p.err("expected 'else'");
    }
    p.b.wrap_from(cp, NodeKind::IfExpr);
    NodeKind::IfExpr
}

fn parse_let(p: &mut Parser<'_>, cp: usize) -> NodeKind {
    p.bump(); // let
    let bcp = p.b.checkpoint();
    // A binding is `name = expr` or a pattern followed by `=`.
    while let Some(t) = p.sig(0) {
        if t.kind == Kind::Equals || t.kind == Kind::EndOfFile || t.kind == Kind::Newline {
            break;
        }
        p.bump();
    }
    if p.kind(0) == Some(Kind::Equals) {
        p.bump();
        p.skip_newlines();
        parse_expr(p);
    } else {
        p.err("expected '=' in a let binding");
    }
    p.b.wrap_from(bcp, NodeKind::LetBinding);
    p.skip_newlines();
    if p.kind(0) == Some(Kind::InKeyword) {
        p.bump();
        p.skip_newlines();
        parse_expr(p);
    } else {
        p.err("expected 'in' after a let binding");
    }
    p.b.wrap_from(cp, NodeKind::LetExpr);
    NodeKind::LetExpr
}

/// `when e is Pat -> body is otherwise -> body`, and `induction` shares the
/// shape. Arms run until something that is not another `is`.
fn parse_match(p: &mut Parser<'_>, cp: usize, kind: NodeKind) -> NodeKind {
    p.bump(); // when / induction
    parse_expr(p);
    p.skip_newlines();
    while p.kind(0) == Some(Kind::IsKeyword) {
        let acp = p.b.checkpoint();
        p.bump(); // is
        let pcp = p.b.checkpoint();
        // The pattern runs to the arrow. Patterns have their own grammar; the
        // tokens are kept under one node until it is written.
        while let Some(t) = p.sig(0) {
            if t.kind == Kind::FatArrow || t.kind == Kind::Arrow || t.kind == Kind::EndOfFile {
                break;
            }
            p.bump();
        }
        p.b.wrap_from(pcp, NodeKind::Pattern);
        if matches!(p.kind(0), Some(Kind::Arrow) | Some(Kind::FatArrow)) {
            p.bump();
        } else {
            p.err("expected '->' in a match arm");
        }
        p.skip_newlines();
        parse_expr(p);
        p.b.wrap_from(acp, NodeKind::MatchArm);
        p.skip_newlines();
    }
    p.b.wrap_from(cp, kind);
    kind
}

/// `act .. end`, and the three block forms that share its shape. The block is
/// a sequence of statements terminated by `end`, and blocks nest.
fn parse_act(p: &mut Parser<'_>, cp: usize, kind: NodeKind) -> NodeKind {
    p.bump(); // act / trying / with / with-timeout
    let mut depth = 1usize;
    while let Some(t) = p.sig(0) {
        match t.kind {
            Kind::EndOfFile => break,
            Kind::EndKeyword => {
                depth -= 1;
                p.bump();
                if depth == 0 {
                    break;
                }
            }
            Kind::ActKeyword | Kind::TryingKeyword => {
                depth += 1;
                p.bump();
            }
            _ => {
                p.bump();
            }
        }
    }
    if depth != 0 {
        p.err("a block was not closed by 'end'");
    }
    p.b.wrap_from(cp, kind);
    parse_field_access(p, cp, kind)
}

fn parse_lambda(p: &mut Parser<'_>, cp: usize) -> NodeKind {
    p.bump(); // backslash
    while matches!(p.kind(0), Some(Kind::Identifier) | Some(Kind::Underscore)) {
        p.bump();
    }
    if matches!(p.kind(0), Some(Kind::Arrow) | Some(Kind::FatArrow)) {
        p.bump();
    } else {
        p.err("expected '->' after lambda parameters");
    }
    p.skip_newlines();
    parse_expr(p);
    p.b.wrap_from(cp, NodeKind::Lambda);
    NodeKind::Lambda
}

/// `for x in xs -> body`, a comprehension. `for` and `in` are both ordinary
/// identifiers/keywords to the lexer, so the shape has to be read here.
fn parse_for(p: &mut Parser<'_>, cp: usize) -> NodeKind {
    p.bump(); // for
    if matches!(p.kind(0), Some(Kind::Identifier) | Some(Kind::Underscore)) {
        p.bump(); // the loop variable
    } else {
        p.err("expected a name after 'for'");
    }
    if p.kind(0) == Some(Kind::InKeyword) {
        p.bump();
    } else {
        p.err("expected 'in' after the loop variable of a 'for'");
    }
    parse_expr(p);
    if matches!(p.kind(0), Some(Kind::Arrow) | Some(Kind::FatArrow)) {
        p.bump();
    } else {
        p.err("expected '->' in a 'for' comprehension");
    }
    p.skip_newlines();
    parse_expr(p);
    p.b.wrap_from(cp, NodeKind::ForExpr);
    NodeKind::ForExpr
}

#[cfg(test)]
mod tests {
    use crate::cst::NodeKind;
    use crate::parser::parse;

    /// The shape of the first definition's body, tokens dropped.
    fn body_shape(expr: &str) -> String {
        let src = format!("Chapter: T\n\nSection: S\n  f : A\n  f (x) =\n   {expr}\n");
        let p = parse(src.as_bytes());
        // Coverage is an invariant of every parse, so assert it here too.
        let lexed = crate::lexer::tokenize(src.as_bytes());
        let in_tree: Vec<_> = p.tree.tokens().copied().collect();
        assert_eq!(in_tree, lexed.tokens, "a token did not reach the tree");
        assert_eq!(p.unparsed_bodies, 0, "body not understood: {expr}");
        assert!(p.errors.is_empty(), "{:?} for {expr}", p.errors);
        let def = p.tree.descendants(NodeKind::Def).into_iter().next().unwrap();
        // Strip the Def wrapper -- its opening text and its ONE closing paren.
        // `trim_end_matches` would eat the body's own closers too.
        let shape = def.shape();
        let inner = shape
            .strip_prefix("(Def (TypeAnnotation (TypeExpr)) (DefEquation (ParamGroup)) ")
            .unwrap_or(&shape);
        inner.strip_suffix(')').unwrap_or(inner).to_string()
    }

    #[test]
    fn multiplication_binds_tighter_than_addition() {
        assert_eq!(body_shape("a + b * c"), "(Bin (Name) (Bin (Name) (Name)))");
        assert_eq!(body_shape("a * b + c"), "(Bin (Bin (Name) (Name)) (Name))");
    }

    #[test]
    fn xor_sits_between_or_and_and() {
        // `a and b xor c or d` groups as `((a and b) xor c) or d`. The numbers
        // in the table are internal; this ORDER is the contract.
        assert_eq!(
            body_shape("a and b xor c or d"),
            "(Bin (Bin (Bin (Name) (Name)) (Name)) (Name))"
        );
    }

    #[test]
    fn caret_is_right_associative_and_star_is_not() {
        assert_eq!(body_shape("a ^ b ^ c"), "(Bin (Name) (Bin (Name) (Name)))");
        assert_eq!(body_shape("a * b * c"), "(Bin (Bin (Name) (Name)) (Name))");
    }

    #[test]
    fn not_swallows_a_comparison_but_stops_before_and() {
        // `not a == b` is `not (a == b)`, because `(not a) == b` type-checks
        // perfectly and is never what anybody meant. `not a and b` is
        // `(not a) and b`.
        assert_eq!(body_shape("not a == b"), "(Unary (Bin (Name) (Name)))");
        assert_eq!(body_shape("not a and b"), "(Bin (Unary (Name)) (Name))");
    }

    #[test]
    fn a_minus_that_abuts_its_operand_is_an_argument() {
        // `f a -2` and `f a - 2` carry identical token KINDS; only the byte
        // offsets separate an argument from a subtraction.
        assert_eq!(body_shape("f a -2"), "(App (App (Name) (Name)) (Unary (Lit)))");
        assert_eq!(body_shape("f a - 2"), "(Bin (App (Name) (Name)) (Lit))");
    }

    #[test]
    fn application_is_left_associative() {
        assert_eq!(body_shape("f a b"), "(App (App (Name) (Name)) (Name))");
    }

    #[test]
    fn a_field_name_may_be_a_keyword() {
        // `span.end.offset` -- `end` is a keyword, and upstream's
        // is-field-name-token admits it. It does NOT admit a TypeIdentifier.
        assert_eq!(
            body_shape("span.end.offset"),
            "(FieldAccess (FieldAccess (Name)))"
        );
    }

    #[test]
    fn a_for_comprehension_has_a_variable_a_list_and_a_body() {
        assert_eq!(body_shape("for p in pats -> g p"), "(ForExpr (Name) (App (Name) (Name)))");
    }

    #[test]
    fn let_in_and_if_then_else_are_whole_expressions() {
        assert_eq!(body_shape("let y = a in y"), "(LetExpr (LetBinding (Name)) (Name))");
        assert_eq!(body_shape("if a then b else c"), "(IfExpr (Name) (Name) (Name))");
    }

    #[test]
    fn a_match_has_one_node_per_arm() {
        let s = body_shape("when e\n    is A -> 1\n    is otherwise -> 2");
        assert_eq!(
            s,
            "(MatchExpr (Name) (MatchArm (Pattern) (Lit)) (MatchArm (Pattern) (Lit)))"
        );
    }
}
