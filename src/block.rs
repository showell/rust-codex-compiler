//! The four block forms: `act`, `trying`, `with` and `with-timeout`.
//!
//! **Two of the four have no `end`, and that is the whole reason this module
//! exists.** A `with` handler runs to the last of its clauses and a
//! `with-timeout` to the end of its body expression; only `act` and `trying`
//! are closed by a keyword. Reading all four as `end`-terminated -- which is
//! what a depth counter over `act`/`end` does -- swallows everything after the
//! handler up to some unrelated `end`, and then reports the `in` that ended
//! the enclosing `let` as missing.
//!
//! ```text
//! let r = with Reader ask          <- `with <effect> <body>`, then clauses
//!   ask (resume) = act             <- a clause: op, params, `=`, body
//!     print-line-uni "side channel"
//!     resume n
//!   end                            <- closes the clause's `act`, not the with
//! in r                             <- the `in` the old reading lost
//! ```
//!
//! **A handler clause's LAST parameter is the resume continuation**, not an
//! argument: `ask (resume)` binds no arguments and `put (v) (resume)` binds
//! one. The tree keeps them all as `ParamGroup`s in order and lets the
//! desugarer take the last, because that split is a meaning and not a shape.
//!
//! **A clause starts on its own line.** The handler's body is an ordinary
//! expression and newlines are significant outside brackets, so `with State
//! put (v) (resume) = ..` written on one line reads `put (v) (resume)` as the
//! body -- an application -- and finds no clauses at all.
//!
//! **A clause needs at least one parameter to be a clause.** Upstream reads
//! the operation name, reads the parameter groups, and if there were none
//! hands back the state it started with -- so a bare identifier after the body
//! is not a clause and is left where it was. We test the lookahead instead of
//! rewinding, which a tree that only moves forward cannot do.
//!
//! `act` statements are `name <- expr` or a bare expression, newline
//! separated, and an `act end` with nothing in it is upstream's `cdx-empty-act`.
//! `trying <n> times ... falling back to ... on failure ... end` has three
//! statement lists and every word in it -- `times`, `falling`, `back`, `to`,
//! `on`, `failure` -- is an ordinary identifier the parser matches by TEXT.

use crate::cst::NodeKind;
use crate::expr::parse_expr;
use crate::parser::Parser;
use crate::token::Kind;

/// `act <stmts> end`.
pub(crate) fn parse_act(p: &mut Parser<'_>, cp: usize) -> NodeKind {
    p.bump(); // act
    p.skip_newlines();
    if stmts_to_end(p, &[]) == 0 {
        p.err("an 'act' block must contain at least one statement");
    }
    p.b.wrap_from(cp, NodeKind::ActBlock);
    NodeKind::ActBlock
}

/// Statements until `end` or the end of the file, stopping early at any of
/// `stops` -- the words that open `trying`'s later sections.
fn stmts_to_end(p: &mut Parser<'_>, stops: &[&[u8]]) -> usize {
    let mut n = 0;
    loop {
        match p.kind(0) {
            // Upstream stops here too, and quietly. A block whose `end` never
            // arrived has swallowed the rest of the file, so it is counted:
            // "0 blocks still flat" was true of a parser that ate everything.
            None | Some(Kind::EndOfFile) => {
                p.unclosed_blocks += 1;
                return n;
            }
            Some(Kind::EndKeyword) => {
                p.bump();
                return n;
            }
            _ => {}
        }
        if let Some(t) = p.sig(0) {
            if stops.iter().any(|w| p.text_is(t, w)) {
                return n;
            }
        }
        act_stmt(p);
        n += 1;
        p.skip_newlines();
    }
}

/// `name <- expr`, or an expression on its own.
fn act_stmt(p: &mut Parser<'_>) {
    let cp = p.b.checkpoint();
    if p.kind(0) == Some(Kind::Identifier) && p.kind(1) == Some(Kind::LeftArrow) {
        p.bump(); // the bound name
        p.bump(); // <-
        parse_expr(p);
        p.b.wrap_from(cp, NodeKind::ActBind);
    } else {
        parse_expr(p);
        p.b.wrap_from(cp, NodeKind::ActStmt);
    }
}

/// `trying <count> times <stmts> [falling back to <stmts>] [on failure
/// <stmts>] end`.
pub(crate) fn parse_trying(p: &mut Parser<'_>, cp: usize) -> NodeKind {
    p.bump(); // trying
    p.skip_newlines();
    if !p.kind(0).is_some_and(is_literal) {
        // Upstream gives up here and takes one token as an error expression.
        p.err("expected an attempt count after 'trying'");
        p.bump();
        p.b.wrap_from(cp, NodeKind::TryExpr);
        return NodeKind::TryExpr;
    }
    p.bump(); // the count
    p.skip_newlines();
    if word(p, b"times") {
        p.bump();
        p.skip_newlines();
    } else {
        p.err("expected 'times' after the attempt count of a 'trying'");
    }

    // The body stops at `end`, at `falling`, or at `on failure`.
    let closed = section(p, NodeKind::TryBody, &[b"falling".as_slice(), b"on".as_slice()]);
    if closed {
        p.b.wrap_from(cp, NodeKind::TryExpr);
        return NodeKind::TryExpr;
    }

    if word(p, b"falling") {
        p.bump();
        p.skip_newlines();
        for w in [b"back".as_slice(), b"to".as_slice()] {
            if word(p, w) {
                p.bump();
                p.skip_newlines();
            } else {
                p.err("expected 'falling back to' before a fallback block");
            }
        }
        if section(p, NodeKind::TryFallback, &[b"on".as_slice()]) {
            p.b.wrap_from(cp, NodeKind::TryExpr);
            return NodeKind::TryExpr;
        }
    }

    // `on failure` -- and a bare `on` that is not followed by `failure` is an
    // ordinary statement, so the second word decides.
    if word(p, b"on") && p.sig(1).is_some_and(|t| p.text_is(t, b"failure")) {
        p.bump();
        p.bump();
        p.skip_newlines();
        section(p, NodeKind::TryFailure, &[]);
    }
    p.b.wrap_from(cp, NodeKind::TryExpr);
    NodeKind::TryExpr
}

/// One statement list of a `trying`. Answers whether it ate the closing `end`.
fn section(p: &mut Parser<'_>, kind: NodeKind, stops: &[&[u8]]) -> bool {
    let scp = p.b.checkpoint();
    let before = p.at();
    stmts_to_end(p, stops);
    let closed = p.toks[before..p.at()]
        .iter()
        .rev()
        .find(|t| !t.kind.is_trivia())
        .is_some_and(|t| t.kind == Kind::EndKeyword);
    p.b.wrap_from(scp, kind);
    closed
}

fn is_literal(k: Kind) -> bool {
    matches!(
        k,
        Kind::IntegerLiteral | Kind::NumberLiteral | Kind::TextLiteral | Kind::CharLiteral
    )
}

/// Is the next significant token this exact word? Every keyword of `trying`
/// is an ordinary identifier, so text is the only test there is.
fn word(p: &Parser<'_>, w: &[u8]) -> bool {
    p.sig(0).is_some_and(|t| t.kind == Kind::Identifier && p.text_is(t, w))
}

/// `with <effect> <body>` and its clauses. NO `end`.
pub(crate) fn parse_handle(p: &mut Parser<'_>, cp: usize) -> NodeKind {
    p.bump(); // with
    if p.sig(0).is_some() {
        p.bump(); // the effect's name, whatever kind of token it is
    }
    parse_expr(p); // the body the handler wraps
    p.skip_newlines();
    // A clause is an operation name followed by at least one parameter group.
    // Without that lookahead the identifier after the body would be eaten as a
    // clause with nothing in it.
    while p.kind(0) == Some(Kind::Identifier) && p.kind(1) == Some(Kind::LeftParen) {
        let ccp = p.b.checkpoint();
        p.bump(); // the operation
        while p.kind(0) == Some(Kind::LeftParen) {
            let pcp = p.b.checkpoint();
            p.bump();
            if p.kind(0) != Some(Kind::RightParen) {
                p.bump(); // the parameter's name
            }
            if p.kind(0) == Some(Kind::RightParen) {
                p.bump();
            } else {
                p.err("expected ')' closing a handler clause parameter");
            }
            p.b.wrap_from(pcp, NodeKind::ParamGroup);
        }
        if p.kind(0) == Some(Kind::Equals) {
            p.bump();
        } else {
            p.err("expected '=' in a handler clause");
        }
        p.skip_newlines();
        parse_expr(p);
        p.b.wrap_from(ccp, NodeKind::HandleClause);
        p.skip_newlines();
    }
    p.b.wrap_from(cp, NodeKind::HandleExpr);
    NodeKind::HandleExpr
}

/// `with-timeout <n> [Effects] <body>`. NO `end` either.
pub(crate) fn parse_with_timeout(p: &mut Parser<'_>, cp: usize) -> NodeKind {
    p.bump(); // with-timeout
    if p.sig(0).is_some() {
        p.bump(); // the timeout
    }
    effect_row(p);
    parse_expr(p);
    p.b.wrap_from(cp, NodeKind::WithTimeout);
    NodeKind::WithTimeout
}

/// `[Console, Device.Block "scope", r]`, taken whole.
///
/// Upstream's `parse-effect-names` separates the names, their scope literals
/// and the row-variable tail, and raises two diagnostics of its own. That
/// structure belongs to the effect row wherever it appears -- every `[Console]
/// Nothing` annotation in the checkout -- and not to this one caller, so it is
/// owed as its own piece of work and shared with `types::parse_effect_type`
/// when it lands.
pub(crate) fn effect_row(p: &mut Parser<'_>) {
    if p.kind(0) != Some(Kind::LeftBracket) {
        p.err("expected '[' opening an effect row");
        return;
    }
    let cp = p.b.checkpoint();
    p.bump();
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
    p.b.wrap_from(cp, NodeKind::EffectRow);
}

#[cfg(test)]
mod tests {
    use crate::cst::NodeKind;
    use crate::parser::parse;

    /// The shape of the first definition's body.
    fn body(expr: &str) -> String {
        let src = format!("Chapter: T\n\nSection: S\n  f : A\n  f (x) =\n   {expr}\n");
        let p = parse(src.as_bytes());
        let lexed = crate::lexer::tokenize(src.as_bytes());
        let in_tree: Vec<_> = p.tree.tokens().copied().collect();
        assert_eq!(in_tree, lexed.tokens, "a token did not reach the tree");
        assert_eq!(p.unparsed_bodies, 0, "body not understood: {expr}");
        assert_eq!(p.unclosed_blocks, 0, "a block was left open: {expr}");
        assert!(p.errors.is_empty(), "{:?} for {expr}", p.errors);
        p.tree
            .descendants(NodeKind::Def)
            .into_iter()
            .next()
            .unwrap()
            .child_nodes()
            .into_iter()
            .find(|n| !matches!(n.kind, NodeKind::TypeAnnotation | NodeKind::DefEquation))
            .expect("a body")
            .shape()
    }

    #[test]
    fn an_act_block_is_one_node_per_statement() {
        assert_eq!(
            body("act\n    v <- get-it\n    print-line-uni v\n   end"),
            "(ActBlock (ActBind (Name)) (ActStmt (App (Name) (Name))))"
        );
    }

    #[test]
    fn a_handler_has_no_end_and_the_let_after_it_survives() {
        // The whole reason this module exists. A depth counter over act/end
        // read the clause's own `end` as the handler's, swallowed the `in`,
        // and reported it missing -- ten files in the checkout.
        assert_eq!(
            body("let r = with Reader ask\n     ask (resume) = act\n       resume 1\n     end\n   in r"),
            "(LetExpr (LetBinding (HandleExpr (Name) \
(HandleClause (ParamGroup) (ActBlock (ActStmt (App (Name) (Lit))))))) (Name))"
        );
    }

    #[test]
    fn a_clause_needs_a_parameter_to_be_a_clause() {
        // A bare identifier after the body is not a clause. Upstream reads the
        // name, finds no parameters and hands back the state it started with;
        // we test the lookahead, because the tree only moves forward.
        let s = body("let r = with Reader ask\n   in r");
        assert_eq!(s, "(LetExpr (LetBinding (HandleExpr (Name))) (Name))");
    }

    #[test]
    fn the_last_clause_parameter_is_the_resume_and_stays_in_order() {
        // The clause has to start on its own line: the handler's BODY is an
        // ordinary expression and newlines are significant outside brackets,
        // so `with State put (v) (resume) = ..` on one line reads `put (v)
        // (resume)` as the body, an application. The tree keeps both
        // parameters in order and the desugarer takes the last as `resume`.
        assert_eq!(
            body("with State body-expr
     put (v) (resume) = resume 0"),
            "(HandleExpr (Name) (HandleClause (ParamGroup) (ParamGroup) (App (Name) (Lit))))"
        );
    }

    #[test]
    fn trying_has_three_statement_lists() {
        assert_eq!(
            body(concat!(
                "trying 3 times\n    do-it\n",
                "   falling back to\n    plan-b\n",
                "   on failure\n    give-up\n   end"
            )),
            "(TryExpr (TryBody (ActStmt (Name))) (TryFallback (ActStmt (Name))) \
(TryFailure (ActStmt (Name))))"
        );
    }

    #[test]
    fn a_with_timeout_carries_its_effect_row_and_its_body() {
        assert_eq!(
            body("with-timeout 30 [Console] 42"),
            "(WithTimeout (EffectRow) (Lit))"
        );
    }

    #[test]
    fn an_act_that_never_meets_its_end_is_counted() {
        // Upstream accepts this in silence -- `ecdsa-p384.codex` ends mid-act
        // and is banked clean -- so it is COUNTED and not an error. Without
        // the count, a block that ate the rest of the file would look exactly
        // like one that closed.
        let src = "Chapter: T\n\nSection: S\n  f : A\n  f (x) =\n   act\n    go\n";
        let p = parse(src.as_bytes());
        assert_eq!(p.unclosed_blocks, 1);
        assert!(p.errors.is_empty(), "{:?}", p.errors);
    }
}
