//! The document layer: chapters, sections, citations, type definitions and
//! definition signatures.
//!
//! Codex has no layout tokens -- the lexer emits neither `Indent` nor `Dedent`
//! -- so structure is read off token COLUMNS, exactly as upstream does it:
//! column 1 is a chapter or section header, column 2 is prose (the lexer has
//! already turned that into trivia), column 3 is a top-level item, and anything
//! deeper is a continuation. A definition's body therefore runs until a
//! definition-starting token appears at or left of the equation name's column.
//!
//! The column test is EQUALITY, not "at least". A chapter ends with a
//! `Page 1 of 3` footer at column 1, and accepting an item anywhere at or
//! right of column 3 reads the `of` in it as a definition.
//!
//! ## What is NOT here yet
//!
//! Expression bodies. They are collected into a `NodeKind::UnparsedBody` and
//! COUNTED, so a dump says how much of the file is still unread rather than
//! letting a swallowed body look like an understood one. `parse.truth` does not
//! inspect bodies -- it records each definition's name, parameter count,
//! annotation count, position and chapter -- so this layer is exactly what that
//! rung can check, and the expression grammar is the next piece of work.

use crate::cst::{Builder, Node, NodeKind};
use crate::token::{Kind, Token};

#[derive(Clone, Debug)]
pub struct ParseError {
    pub msg: String,
    pub line: u32,
    pub col: u32,
}

pub struct Parsed {
    pub tree: Node,
    pub errors: Vec<ParseError>,
    /// Bodies collected but not yet given structure. Reported, never hidden.
    pub unparsed_bodies: usize,
    /// Annotations whose type the type grammar could not finish reading.
    pub unread_types: usize,
    /// Type definitions whose body the grammar could not finish reading.
    pub unread_type_defs: usize,
    /// `act` and `trying` blocks that ran to the end of the file without
    /// meeting their `end`.
    pub unclosed_blocks: usize,
}

/// The column a top-level item sits at. Upstream compares against the literal
/// 3 in a dozen places; naming it makes those comparisons readable.
const TOP_LEVEL_COL: u32 = 3;

pub(crate) struct Parser<'a> {
    pub(crate) b: Builder,
    pub(crate) src: &'a [u8],
    pub(crate) toks: Vec<Token>,
    pub(crate) errors: Vec<ParseError>,
    pub(crate) unparsed_bodies: usize,
    pub(crate) unread_types: usize,
    pub(crate) unread_type_defs: usize,
    pub(crate) unclosed_blocks: usize,
    /// Newlines are skipped inside brackets and significant outside them. This
    /// is upstream's `paren-depth` and it is the whole reason a multi-line
    /// application is an error at the top level and fine inside parentheses.
    pub(crate) paren_depth: u32,
}

impl<'a> Parser<'a> {
    /// Is this token exactly this word? `for` is a keyword the lexer does not
    /// know about -- it arrives as an ordinary identifier -- so the parser is
    /// the only place that can tell.
    pub(crate) fn text_is(&self, t: Token, word: &[u8]) -> bool {
        t.text(self.src) == word
    }

    /// The index of the next token the builder has not eaten.
    pub(crate) fn at(&self) -> usize {
        self.b.consumed()
    }

    /// The next `n`th token that the parser can make a decision on. Spaces and
    /// skipped prose are ours, not upstream's, so they never influence a
    /// choice -- but they are still eaten into the tree in order.
    pub(crate) fn sig(&self, n: usize) -> Option<Token> {
        self.toks[self.at()..]
            .iter()
            .filter(|t| !t.kind.is_trivia())
            .nth(n)
            .copied()
    }

    pub(crate) fn kind(&self, n: usize) -> Option<Kind> {
        self.sig(n).map(|t| t.kind)
    }

    pub(crate) fn done(&self) -> bool {
        self.at() >= self.toks.len()
    }

    /// Eat trivia into whatever node is open, then eat one real token.
    pub(crate) fn bump(&mut self) -> Option<Token> {
        while self.toks.get(self.at()).is_some_and(|t| t.kind.is_trivia()) {
            self.b.eat();
        }
        self.b.eat()
    }

    /// Eat trivia only, so it attaches to the enclosing node rather than to
    /// the construct about to start.
    pub(crate) fn drift(&mut self) {
        while self.toks.get(self.at()).is_some_and(|t| t.kind.is_trivia()) {
            self.b.eat();
        }
    }

    pub(crate) fn eat_to_end_of_line(&mut self) {
        while let Some(k) = self.kind(0) {
            if k == Kind::Newline || k == Kind::EndOfFile {
                break;
            }
            self.bump();
        }
    }

    pub(crate) fn skip_newlines(&mut self) {
        while self.kind(0) == Some(Kind::Newline) {
            self.bump();
        }
    }

    pub(crate) fn err(&mut self, msg: impl Into<String>) {
        let (line, col) = self.sig(0).map(|t| (t.line, t.col)).unwrap_or((0, 0));
        self.errors.push(ParseError { msg: msg.into(), line, col });
    }
}

/// Upstream's `is-claim-or-def-start`: what may begin a top-level item, and so
/// what ends the body of the one before it.
pub(crate) fn starts_an_item(k: Kind) -> bool {
    matches!(
        k,
        Kind::Identifier
            | Kind::TypeIdentifier
            | Kind::ClaimKeyword
            | Kind::ProofKeyword
            | Kind::MutableKeyword
            | Kind::EffectKeyword
            | Kind::ClassKeyword
            | Kind::InstanceKeyword
            | Kind::UnitKeyword
            | Kind::CitesKeyword
            | Kind::QuotesKeyword
            | Kind::GroundsKeyword
            | Kind::PunctualKeyword
    )
}

pub fn parse(src: &[u8]) -> Parsed {
    let lexed = crate::lexer::tokenize(src);
    let toks = lexed.tokens;
    let mut p = Parser {
        b: Builder::new(toks.clone()),
        src,
        toks,
        errors: Vec::new(),
        unparsed_bodies: 0,
        unread_types: 0,
        unread_type_defs: 0,
        unclosed_blocks: 0,
        paren_depth: 0,
    };

    while !p.done() {
        p.drift();
        if p.done() {
            break;
        }
        let Some(t) = p.sig(0) else {
            // Only trivia left; it has already been eaten by drift().
            break;
        };

        match t.kind {
            Kind::EndOfFile => {
                p.bump();
            }
            Kind::Newline => {
                p.bump();
            }
            // `Chapter: Name` and `Section: Name` are the only things at the
            // left margin, and both are a TypeIdentifier followed by a colon.
            Kind::TypeIdentifier if t.col == 1 && p.kind(1) == Some(Kind::Colon) => {
                let word = t.text(src);
                let kind = if word == b"Section" {
                    NodeKind::SectionHeader
                } else {
                    NodeKind::ChapterHeader
                };
                p.b.start(kind);
                p.eat_to_end_of_line();
                p.b.end();
            }
            // Three top-level declarations share a shape: a keyword and the
            // rest of its line. `grounds` is one of them, and treating it as a
            // definition is what made the compiler's own `opening.codex`,
            // `BootPaint.codex` and `X86_64Compound.codex` report a parse
            // error -- three files that must be clean by definition, since the
            // compiler is built from them.
            Kind::CitesKeyword => {
                p.b.start(NodeKind::Cites);
                p.eat_to_end_of_line();
                p.b.end();
            }
            Kind::GroundsKeyword => {
                p.b.start(NodeKind::Grounds);
                p.eat_to_end_of_line();
                p.b.end();
            }
            Kind::QuotesKeyword => {
                p.b.start(NodeKind::Quotes);
                p.eat_to_end_of_line();
                p.b.end();
            }
            // `effect` is checked before the type-definition test because it
            // has no `=` and would otherwise fall through to parse_def.
            Kind::EffectKeyword if t.col == TOP_LEVEL_COL => {
                crate::decl::parse_effect_def(&mut p)
            }
            _ if t.col == TOP_LEVEL_COL && looks_like_type_def(&p) => {
                crate::typedef::parse_type_def(&mut p, t)
            }
            _ if t.col == TOP_LEVEL_COL && starts_an_item(t.kind) => parse_def(&mut p, src, t),
            _ => {
                // Whatever this is, it is not a top-level item, and upstream
                // answers the same way: skip to the next line. Taking one
                // token instead would re-enter this loop mid-line and read a
                // word out of the middle of it as a definition -- which is
                // exactly what the `Page 1 of 3` footer produced, an item
                // called `of` at column 8.
                p.b.start(NodeKind::Loose);
                p.eat_to_end_of_line();
                p.b.end();
            }
        }
    }

    let tree = p.b.finish().expect("the builder guarantees full coverage");
    Parsed {
        tree,
        errors: p.errors,
        unparsed_bodies: p.unparsed_bodies,
        unread_types: p.unread_types,
        unread_type_defs: p.unread_type_defs,
        unclosed_blocks: p.unclosed_blocks,
    }
}

/// `Name = record { .. }`, `Name = | A | B`, `Name a b = ..`, and the `mutable`
/// / `effect` / `class` / `instance` / `unit` forms. A value definition never
/// has a TypeIdentifier for a name, which is what separates the two.
fn looks_like_type_def(p: &Parser<'_>) -> bool {
    let Some(first) = p.sig(0) else { return false };
    let start = match first.kind {
        Kind::MutableKeyword
        | Kind::EffectKeyword
        | Kind::ClassKeyword
        | Kind::InstanceKeyword
        | Kind::UnitKeyword => 1,
        Kind::TypeIdentifier => 0,
        _ => return false,
    };
    if p.kind(start) != Some(Kind::TypeIdentifier) {
        return false;
    }
    // Skip type parameters: `Maybe a`, `Either a b`, `Iter (a)`. Missing the
    // paren form does not fail loudly -- the definition parses perfectly as a
    // VALUE definition whose name happens to be capitalised, and 26 of them in
    // the checkout did.
    let mut n = start + 1;
    while crate::typedef::starts_type_params(p, n) {
        n += if p.kind(n) == Some(Kind::LeftParen) { 3 } else { 1 };
    }
    p.kind(n) == Some(Kind::Equals)
}

fn parse_def(p: &mut Parser<'_>, src: &[u8], first: Token) {
    p.b.start(NodeKind::Def);

    // `punctual [budget] name : T` -- a modifier, and then an ordinary
    // definition. It publishes `(ann "hard-realtime" <name> <budget>)` in the
    // chapter header, and until it was read here the definition BEFORE it
    // swallowed it: `punctual` was not in `starts_an_item`, so nothing ended
    // the previous body.
    if p.kind(0) == Some(Kind::PunctualKeyword) {
        let pcp = p.b.checkpoint();
        p.bump();
        if p.kind(0) == Some(Kind::IntegerLiteral) {
            p.bump(); // the budget
        }
        p.b.wrap_from(pcp, NodeKind::Punctual);
    }

    // `name : Type` on its own line, optionally `name : Type = value`.
    let mut saw_equals_on_annotation = false;
    if p.kind(1) == Some(Kind::Colon) {
        p.b.start(NodeKind::TypeAnnotation);
        p.bump(); // the name
        p.bump(); // the colon
        p.b.start(NodeKind::TypeExpr);
        crate::types::parse_type(p);
        // Whatever the type grammar declined still belongs to the annotation.
        // It is kept under Error and COUNTED: a type read halfway must not
        // look like a type read whole.
        match p.kind(0) {
            Some(Kind::Equals) => saw_equals_on_annotation = true,
            Some(Kind::Newline) | Some(Kind::EndOfFile) | None => {}
            _ => {
                p.b.start(NodeKind::Error);
                p.unread_types += 1;
                while let Some(k) = p.kind(0) {
                    if k == Kind::Newline || k == Kind::EndOfFile || k == Kind::Equals {
                        if k == Kind::Equals {
                            saw_equals_on_annotation = true;
                        }
                        break;
                    }
                    p.bump();
                }
                p.b.end();
            }
        }
        p.b.end(); // TypeExpr
        p.b.end(); // TypeAnnotation
    }

    if saw_equals_on_annotation {
        // The constant form: `cc-space : Integer = char-code ' '`. No equation
        // line, no parameters, and the name is the annotation's.
        p.b.start(NodeKind::DefEquation);
        p.b.end();
        p.bump(); // the `=`
        body(p, first.col);
        p.b.end(); // Def
        return;
    }

    p.skip_newlines();

    // The equation line: `name (a) (b) = body`. Upstream reads the name here
    // and not from the annotation, which is why parse.truth's position is this
    // line and not the one above it.
    let Some(name) = p.sig(0) else {
        p.b.end();
        return;
    };
    if !starts_an_item(name.kind) {
        // An annotation with no equation. Real in the wild (a declaration in a
        // class body), and not an error here.
        p.b.end();
        return;
    }
    p.b.start(NodeKind::DefEquation);
    if name.kind == Kind::ProofKeyword {
        p.bump();
    }
    p.bump(); // the name
    while p.kind(0) == Some(Kind::LeftParen) {
        p.b.start(NodeKind::ParamGroup);
        p.bump(); // (
        if matches!(p.kind(0), Some(Kind::Identifier) | Some(Kind::Underscore)) {
            p.bump();
        }
        if p.kind(0) == Some(Kind::RightParen) {
            p.bump();
        } else {
            p.err("expected ')' to close a parameter");
        }
        p.b.end();
    }
    p.b.end(); // DefEquation

    if p.kind(0) == Some(Kind::Equals) {
        p.bump();
        body(p, name.col);
    } else {
        p.err(format!(
            "expected '=' after the parameters of '{}'",
            String::from_utf8_lossy(&name.text(src))
        ));
        eat_item_body(p, name.col);
    }

    p.b.end(); // Def
}

/// A definition body is one expression, parsed with the equation name's column
/// as the floor: the binary loop stops at any token at or left of it, which is
/// how the next definition ends this one.
fn body(p: &mut Parser<'_>, def_col: u32) {
    // The body almost always begins on the line after the `=`, so the newline
    // has to go first. Upstream does the same (`skip-newlines` before
    // `parse-def-body-seq`); without it the expression parser meets a Newline
    // in atom position, calls it an error and hands the whole body back.
    p.skip_newlines();
    crate::expr::parse_expr_col(p, def_col);
    // Anything the expression grammar declined to take still belongs to this
    // body. It is kept under a name that says it was not understood, and it is
    // counted, so an unread body cannot pass for an understood one.
    if let Some(t) = p.sig(0) {
        let unread = !(t.kind == Kind::EndOfFile || (t.col <= def_col && starts_an_item(t.kind)));
        if unread {
            if in_prose_block(p) {
                eat_prose_block(p);
            } else {
                p.b.start(NodeKind::UnparsedBody);
                p.unparsed_bodies += 1;
                eat_item_body(p, def_col);
                p.b.end();
            }
        }
    }
}

/// Are we sitting under a prose line?
///
/// A line at column 2 is prose and the lexer has already turned it into
/// trivia, but the lines UNDER it -- indented past the top-level column --
/// continue that prose and are not code. Upstream keeps skipping while
/// `column > 3`. Looking back for the trivia is how we know a run of
/// deeply-indented words is a paragraph and not an unread expression.
pub(crate) fn in_prose_block(p: &Parser<'_>) -> bool {
    let mut i = p.at();
    while i > 0 {
        i -= 1;
        match p.toks[i].kind {
            Kind::SkippedProse => return true,
            Kind::Newline | Kind::Spaces => continue,
            _ => return false,
        }
    }
    false
}

pub(crate) fn eat_prose_block(p: &mut Parser<'_>) {
    p.b.start(NodeKind::ProseBlock);
    loop {
        p.eat_to_end_of_line();
        // Take the newline, then decide whether the next line is still prose.
        if p.kind(0) == Some(Kind::Newline) {
            p.bump();
        } else {
            break;
        }
        if !prose_continues(p) {
            break;
        }
    }
    p.b.end();
}

/// Does the block go on after the line just consumed?
///
/// It does if the next line is indented past the top-level column, and it also
/// does if -- ACROSS ONE OR MORE BLANK LINES -- the next line is another prose
/// line, which the lexer has already ruled on by making it `SkippedProse`.
/// Stopping at the blank line left the paragraph after it looking like an
/// unread body, which is a phenomenon of paragraph spacing and not a fact
/// about the grammar.
fn prose_continues(p: &Parser<'_>) -> bool {
    let mut i = p.at();
    loop {
        match p.toks.get(i) {
            None => return false,
            Some(t) => match t.kind {
                Kind::SkippedProse => return true,
                Kind::Spaces | Kind::Newline => i += 1,
                Kind::EndOfFile => return false,
                _ => return t.col > TOP_LEVEL_COL,
            },
        }
    }
}

/// Consume up to the next top-level item, which upstream defines as a
/// definition-starting token at or left of the current item's column.
fn eat_item_body(p: &mut Parser<'_>, col: u32) {
    // The item's own first token is still ahead of us on the first call, so
    // always take one before testing.
    if !p.done() {
        p.bump();
    }
    while let Some(t) = p.sig(0) {
        if t.kind == Kind::EndOfFile {
            break;
        }
        if t.col <= col && starts_an_item(t.kind) {
            break;
        }
        p.bump();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cst::NodeKind;

    fn doc(src: &str) -> Parsed {
        let p = parse(src.as_bytes());
        // Coverage is an invariant of every parse, not a separate test.
        let lexed = crate::lexer::tokenize(src.as_bytes());
        let in_tree: Vec<_> = p.tree.tokens().copied().collect();
        assert_eq!(in_tree, lexed.tokens, "a token did not reach the tree");
        p
    }

    fn defs(src: &str) -> Vec<(String, usize, usize)> {
        let p = doc(src);
        p.tree
            .descendants(NodeKind::Def)
            .iter()
            .filter_map(|d| {
                let eq = d.children_of(NodeKind::DefEquation).next();
                let name = eq
                    .and_then(|e| e.tokens().find(|t| {
                        matches!(t.kind, Kind::Identifier | Kind::TypeIdentifier)
                    }))
                    .or_else(|| {
                        d.children_of(NodeKind::TypeAnnotation)
                            .next()
                            .and_then(|a| a.tokens().next())
                    })
                    .map(|t| String::from_utf8_lossy(t.text(src.as_bytes())).into_owned())?;
                let params = eq.map(|e| e.count(NodeKind::ParamGroup)).unwrap_or(0);
                Some((name, params, d.count(NodeKind::TypeAnnotation)))
            })
            .collect()
    }

    #[test]
    fn an_annotation_and_its_equation_are_one_definition() {
        let d = defs("Chapter: T\n\nSection: S\n  f : Integer -> Integer\n  f (x) = x\n");
        assert_eq!(d, vec![("f".to_string(), 1, 1)]);
    }

    #[test]
    fn the_constant_form_has_no_equation_and_no_parameters() {
        // `cc-space : Integer = char-code ' '` -- the `=` arrives on the
        // annotation line, so there is no second line to read a name from.
        let d = defs("Chapter: T\n\nSection: S\n  cc-space : Integer = char-code ' '\n");
        assert_eq!(d, vec![("cc-space".to_string(), 0, 1)]);
    }

    #[test]
    fn parameters_are_counted_per_group() {
        let d = defs("Chapter: T\n\nSection: S\n  g : A, B -> C\n  g (a) (b) = a\n");
        assert_eq!(d, vec![("g".to_string(), 2, 1)]);
    }

    #[test]
    fn grounds_and_cites_are_declarations_not_definitions() {
        // Treating `grounds` as a definition is what made three of the
        // compiler's own chapters report a parse error.
        let p = doc("Chapter: Opening\n  grounds Device.Port, Device.Block\n  cites Foreword chapter Maybe\n");
        assert_eq!(p.tree.descendants(NodeKind::Def).len(), 0);
        assert_eq!(p.tree.descendants(NodeKind::Grounds).len(), 1);
        assert_eq!(p.tree.descendants(NodeKind::Cites).len(), 1);
        assert!(p.errors.is_empty(), "{:?}", p.errors);
    }

    #[test]
    fn a_page_footer_is_not_a_definition() {
        // `Page 1 of 3` sits at column 1. Accepting an item at any column at
        // or right of 3 read the `of` in it as a definition named `of`.
        let p = doc("Chapter: T\n\nSection: S\n  f : A\n  f (x) = x\n\nPage 1 of 3\n");
        assert_eq!(p.tree.descendants(NodeKind::Def).len(), 1);
    }

    #[test]
    fn a_body_ends_where_the_next_definition_begins() {
        let d = defs(concat!(
            "Chapter: T\n\nSection: S\n",
            "  f : A\n  f (x) =\n   let y = x\n   in y\n",
            "  g : A\n  g (x) = x\n"
        ));
        assert_eq!(d.len(), 2);
        assert_eq!(d[0].0, "f");
        assert_eq!(d[1].0, "g");
    }

    #[test]
    fn a_type_definition_is_not_a_value_definition() {
        let p = doc("Chapter: T\n\nSection: S\n  Colour =\n   | Red\n   | Green\n");
        assert_eq!(p.tree.descendants(NodeKind::TypeDef).len(), 1);
        assert_eq!(p.tree.descendants(NodeKind::Def).len(), 0);
    }

    #[test]
    fn sections_and_the_chapter_are_found() {
        let p = doc("Chapter: T\n\nSection: One\n\nSection: Two\n");
        assert_eq!(p.tree.descendants(NodeKind::ChapterHeader).len(), 1);
        assert_eq!(p.tree.descendants(NodeKind::SectionHeader).len(), 2);
    }
}
