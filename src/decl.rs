//! Declaration forms: things at the top level that are neither a value
//! definition nor a type definition.
//!
//! ```text
//! effect Audio where
//!   audio-play : Text -> Nothing
//!   audio-stop : Nothing
//! ```
//!
//! None of them has an `=` where a definition wants one, so each one that is
//! not written here falls through to `parse_def` and reports
//! `expected '=' after the parameters of 'effect'` -- 31 files' worth, and the
//! same shape for `claim` (69), `instance` (10) and `class` (2).
//!
//! **An operation is `ident :` and the block ends at the first line that is
//! not.** There is no `end` and no indentation rule: `parse-effect-ops` reads
//! while it sees an identifier followed by a colon and stops otherwise, which
//! is what lets the next definition follow with nothing between them.
//!
//! `where` is optional in the grammar -- upstream advances past it only if it
//! is there -- though every occurrence in the checkout has it.

use crate::cst::NodeKind;
use crate::parser::Parser;
use crate::token::Kind;

/// `class [<Super> => ] <Name> [where] <method> : <type> ...`
///
/// A class declares a DICTIONARY RECORD: `class Showable where to-text : a ->
/// Text` becomes `(rec-def "ShowableDict" (tparams "a") (fields (rec-field
/// "to-text-impl" (a-fun (a-named "a") (a-named "Text")))))`. Its methods have
/// exactly the shape an effect's operations have, and upstream parses them
/// with the same function, so they share a node kind here too.
///
/// **A superclass is written in front with a fat arrow**, and it is told from
/// the class's own name only by looking two tokens ahead: `class Eq => Ord
/// where` names Ord and `class Ord where` names Ord as well.
pub(crate) fn parse_class_def(p: &mut Parser<'_>) {
    p.b.start(NodeKind::ClassDef);
    p.bump(); // class
    if p.sig(0).is_some() {
        p.bump(); // the name -- or the SUPERCLASS, which the arrow decides
    }
    if p.kind(0) == Some(Kind::Identifier) && p.kind(1) == Some(Kind::FatArrow) {
        let scp = p.b.checkpoint();
        p.bump(); // =>'s left, already eaten above; this is the real name
        p.bump(); // =>
        p.b.wrap_from(scp, NodeKind::Superclass);
        if p.sig(0).is_some() {
            p.bump(); // the class's own name
        }
    }
    ops_block(p);
    p.b.end();
}

/// `instance <Class> <type> [where] <method> (p) .. = <expr> ...`
///
/// Only the class NAME matters to the chapter header -- a dictionary is
/// parameterised when its class has more than one instance -- but the methods
/// are read rather than skipped, because a body nobody parses is a body that
/// comes back as an unread one.
pub(crate) fn parse_instance_def(p: &mut Parser<'_>) {
    p.b.start(NodeKind::InstanceDef);
    p.bump(); // instance
    if p.sig(0).is_some() {
        p.bump(); // the class
    }
    // The instantiated type: `Integer`, or `(List Integer)` taken whole.
    if p.kind(0) == Some(Kind::LeftParen) {
        let mut depth = 0usize;
        while let Some(t) = p.sig(0) {
            match t.kind {
                Kind::LeftParen => depth += 1,
                Kind::RightParen => depth -= 1,
                Kind::EndOfFile => break,
                _ => {}
            }
            p.bump();
            if depth == 0 {
                break;
            }
        }
    } else if p.sig(0).is_some() {
        p.bump();
    }
    if p.kind(0) == Some(Kind::WhereKeyword) {
        p.bump();
        p.skip_newlines();
    }
    while p.kind(0) == Some(Kind::Identifier) {
        let mcp = p.b.checkpoint();
        p.bump(); // the method
        while p.kind(0) == Some(Kind::LeftParen) {
            let pcp = p.b.checkpoint();
            p.bump();
            if p.kind(0) != Some(Kind::RightParen) {
                p.bump();
            }
            if p.kind(0) == Some(Kind::RightParen) {
                p.bump();
            } else {
                p.err("expected ')' closing an instance method parameter");
            }
            p.b.wrap_from(pcp, NodeKind::ParamGroup);
        }
        if p.kind(0) != Some(Kind::Equals) {
            // Not a method after all; leave it for the document layer.
            p.b.wrap_from(mcp, NodeKind::Error);
            break;
        }
        p.bump();
        p.skip_newlines();
        crate::expr::parse_expr(p);
        p.b.wrap_from(mcp, NodeKind::InstanceMethod);
        p.skip_newlines();
    }
    p.b.end();
}

/// `<op> : <type>` lines, ending at the first line that is not one. Shared by
/// `effect` and `class`, as upstream shares `parse-effect-ops`.
fn ops_block(p: &mut Parser<'_>) {
    if p.kind(0) == Some(Kind::WhereKeyword) {
        p.bump();
        p.skip_newlines();
    }
    while p.kind(0) == Some(Kind::Identifier) && p.kind(1) == Some(Kind::Colon) {
        let ocp = p.b.checkpoint();
        p.bump(); // the operation
        p.bump(); // the colon
        crate::types::parse_type(p);
        p.b.wrap_from(ocp, NodeKind::EffectOp);
        p.skip_newlines();
    }
}

/// `effect <Name> where <op> : <type> ...`
pub(crate) fn parse_effect_def(p: &mut Parser<'_>) {
    p.b.start(NodeKind::EffectDef);
    p.bump(); // effect
    if p.sig(0).is_some() {
        p.bump(); // the effect's name, whatever kind of token it is
    }
    ops_block(p);
    p.b.end();
}
