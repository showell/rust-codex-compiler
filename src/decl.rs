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

/// `effect <Name> where <op> : <type> ...`
pub(crate) fn parse_effect_def(p: &mut Parser<'_>) {
    p.b.start(NodeKind::EffectDef);
    p.bump(); // effect
    if p.sig(0).is_some() {
        p.bump(); // the effect's name, whatever kind of token it is
    }
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
    p.b.end();
}
