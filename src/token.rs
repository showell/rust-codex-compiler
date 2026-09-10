//! The token vocabulary, and what a lossless stream adds to it.
//!
//! `Kind` is Cobblestone's `TokenKind` from `Syntax/Token.codex`, all 92
//! variants, spelled the way the ladder's `lex.truth` spells them so a dump
//! can be diffed against it without a translation table.
//!
//! `Trivia` is ours. Cobblestone's lexer drops spaces on the floor and skips a
//! prose line without recording it, which is fine for a compiler and useless
//! for a linter. We keep both, which is what makes the stream lossless and
//! makes `concat(tokens) == source` a check the source itself can answer.
//!
//! Two variants of `Kind` are DEAD in Cobblestone and kept only so the
//! vocabulary matches: `Indent` and `Dedent` are declared and never
//! constructed -- the lexer emits no layout tokens at all. Do not implement a
//! layout algorithm for them.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Kind {
    EndOfFile,
    Newline,
    Indent,
    Dedent,
    IntegerLiteral,
    NumberLiteral,
    TextLiteral,
    CharLiteral,
    TrueKeyword,
    FalseKeyword,
    Identifier,
    TypeIdentifier,
    ProseText,
    ChapterHeader,
    SectionHeader,
    QuotesKeyword,
    TrustingKeyword,
    AboveKeyword,
    LetKeyword,
    InKeyword,
    BetweenKeyword,
    AndKeyword,
    OrKeyword,
    XorKeyword,
    NotKeyword,
    IfKeyword,
    IsKeyword,
    OtherwiseKeyword,
    ThenKeyword,
    ElseKeyword,
    WhenKeyword,
    WhereKeyword,
    SuchThatKeyword,
    ActKeyword,
    EndKeyword,
    RecordKeyword,
    CitesKeyword,
    GroundsKeyword,
    ClaimKeyword,
    ProofKeyword,
    QedKeyword,
    InductionKeyword,
    ForAllKeyword,
    ThereExistsKeyword,
    LinearKeyword,
    MutableKeyword,
    PunctualKeyword,
    BoundedKeyword,
    EffectKeyword,
    ClassKeyword,
    InstanceKeyword,
    WithKeyword,
    WithTimeoutKeyword,
    TryingKeyword,
    LazyKeyword,
    ForKeyword,
    Equals,
    Colon,
    Arrow,
    LeftArrow,
    Pipe,
    PipeForward,
    Ampersand,
    Plus,
    Minus,
    Star,
    Slash,
    Caret,
    ColonColon,
    DoubleEquals,
    NotEquals,
    LessThan,
    GreaterThan,
    LessOrEqual,
    GreaterOrEqual,
    TripleEquals,
    Tilde,
    TildeZero,
    FatArrow,
    LeftParen,
    RightParen,
    LeftBracket,
    RightBracket,
    LeftBrace,
    RightBrace,
    Comma,
    Dot,
    Underscore,
    Backslash,
    ErrorToken,
    UnitKeyword,
    RevisedKeyword,
    /// Runs of ASCII space. Cobblestone's `skip-spaces` discards these.
    Spaces,
    /// A prose line skipped by `skip-prose-line` because column 1 held exactly
    /// one space and prose mode was off. Cobblestone reaches it, consumes it
    /// and records nothing.
    SkippedProse,
    /// A byte the `char-code` alphabet does not map -- a carriage return, in
    /// every file that has one. `scan-token`'s FIRST branch is `if c == cc-cr
    /// then scan-token (advance-char s)`, and `cc-cr` is `-1`, the value
    /// `char-code-at` answers for exactly these bytes. Cobblestone consumes
    /// them and records nothing; we record them as trivia so the file still
    /// rebuilds by concatenation.
    Unmapped,
}

impl Kind {
    /// Is this ours rather than Cobblestone's? Filtering these out is exactly
    /// the projection that must equal `lex.truth`.
    pub fn is_trivia(self) -> bool {
        matches!(self, Kind::Spaces | Kind::SkippedProse | Kind::Unmapped)
    }

    /// A reserved word: every kind the lexer names as one.
    pub fn is_keyword(self) -> bool {
        self.name().ends_with("Keyword")
    }

    /// Layout, not syntax: the tokens the lexer emits to describe where lines
    /// and blocks begin. Cobblestone's parser consumes them for structure and
    /// they never spell an operator or a literal.
    ///
    /// **`is_trivia` IS NOT THE SAME QUESTION AND ANSWERING IT COST A COUNTER.**
    /// That predicate means "ours rather than Cobblestone's" -- a projection
    /// for `lex.truth` -- so a Newline passes it. `desugar::binary` picked its
    /// operator with `!is_trivia` and, wherever a continuation line began with
    /// the operator, took the NEWLINE as the operator token: nine of them in
    /// `ringplug-source.codex`, each falling through `binary_op` to `&`.
    pub fn is_layout(self) -> bool {
        matches!(self, Kind::Newline | Kind::Indent | Kind::Dedent)
    }

    /// The spelling `lex.truth` uses.
    pub fn name(self) -> &'static str {
        match self {
            Kind::EndOfFile => "EndOfFile",
            Kind::Newline => "Newline",
            Kind::Indent => "Indent",
            Kind::Dedent => "Dedent",
            Kind::IntegerLiteral => "IntegerLiteral",
            Kind::NumberLiteral => "NumberLiteral",
            Kind::TextLiteral => "TextLiteral",
            Kind::CharLiteral => "CharLiteral",
            Kind::TrueKeyword => "TrueKeyword",
            Kind::FalseKeyword => "FalseKeyword",
            Kind::Identifier => "Identifier",
            Kind::TypeIdentifier => "TypeIdentifier",
            Kind::ProseText => "ProseText",
            Kind::ChapterHeader => "ChapterHeader",
            Kind::SectionHeader => "SectionHeader",
            Kind::QuotesKeyword => "QuotesKeyword",
            Kind::TrustingKeyword => "TrustingKeyword",
            Kind::AboveKeyword => "AboveKeyword",
            Kind::LetKeyword => "LetKeyword",
            Kind::InKeyword => "InKeyword",
            Kind::BetweenKeyword => "BetweenKeyword",
            Kind::AndKeyword => "AndKeyword",
            Kind::OrKeyword => "OrKeyword",
            Kind::XorKeyword => "XorKeyword",
            Kind::NotKeyword => "NotKeyword",
            Kind::IfKeyword => "IfKeyword",
            Kind::IsKeyword => "IsKeyword",
            Kind::OtherwiseKeyword => "OtherwiseKeyword",
            Kind::ThenKeyword => "ThenKeyword",
            Kind::ElseKeyword => "ElseKeyword",
            Kind::WhenKeyword => "WhenKeyword",
            Kind::WhereKeyword => "WhereKeyword",
            Kind::SuchThatKeyword => "SuchThatKeyword",
            Kind::ActKeyword => "ActKeyword",
            Kind::EndKeyword => "EndKeyword",
            Kind::RecordKeyword => "RecordKeyword",
            Kind::CitesKeyword => "CitesKeyword",
            Kind::GroundsKeyword => "GroundsKeyword",
            Kind::ClaimKeyword => "ClaimKeyword",
            Kind::ProofKeyword => "ProofKeyword",
            Kind::QedKeyword => "QedKeyword",
            Kind::InductionKeyword => "InductionKeyword",
            Kind::ForAllKeyword => "ForAllKeyword",
            Kind::ThereExistsKeyword => "ThereExistsKeyword",
            Kind::LinearKeyword => "LinearKeyword",
            Kind::MutableKeyword => "MutableKeyword",
            Kind::PunctualKeyword => "PunctualKeyword",
            Kind::BoundedKeyword => "BoundedKeyword",
            Kind::EffectKeyword => "EffectKeyword",
            Kind::ClassKeyword => "ClassKeyword",
            Kind::InstanceKeyword => "InstanceKeyword",
            Kind::WithKeyword => "WithKeyword",
            Kind::WithTimeoutKeyword => "WithTimeoutKeyword",
            Kind::TryingKeyword => "TryingKeyword",
            Kind::LazyKeyword => "LazyKeyword",
            Kind::ForKeyword => "ForKeyword",
            Kind::Equals => "Equals",
            Kind::Colon => "Colon",
            Kind::Arrow => "Arrow",
            Kind::LeftArrow => "LeftArrow",
            Kind::Pipe => "Pipe",
            Kind::PipeForward => "PipeForward",
            Kind::Ampersand => "Ampersand",
            Kind::Plus => "Plus",
            Kind::Minus => "Minus",
            Kind::Star => "Star",
            Kind::Slash => "Slash",
            Kind::Caret => "Caret",
            Kind::ColonColon => "ColonColon",
            Kind::DoubleEquals => "DoubleEquals",
            Kind::NotEquals => "NotEquals",
            Kind::LessThan => "LessThan",
            Kind::GreaterThan => "GreaterThan",
            Kind::LessOrEqual => "LessOrEqual",
            Kind::GreaterOrEqual => "GreaterOrEqual",
            Kind::TripleEquals => "TripleEquals",
            Kind::Tilde => "Tilde",
            Kind::TildeZero => "TildeZero",
            Kind::FatArrow => "FatArrow",
            Kind::LeftParen => "LeftParen",
            Kind::RightParen => "RightParen",
            Kind::LeftBracket => "LeftBracket",
            Kind::RightBracket => "RightBracket",
            Kind::LeftBrace => "LeftBrace",
            Kind::RightBrace => "RightBrace",
            Kind::Comma => "Comma",
            Kind::Dot => "Dot",
            Kind::Underscore => "Underscore",
            Kind::Backslash => "Backslash",
            Kind::ErrorToken => "ErrorToken",
            Kind::UnitKeyword => "UnitKeyword",
            Kind::RevisedKeyword => "RevisedKeyword",
            Kind::Spaces => "Spaces",
            Kind::SkippedProse => "SkippedProse",
            Kind::Unmapped => "Unmapped",
        }
    }
}

/// A token, or a piece of trivia. Positions are exactly Cobblestone's: `offset`
/// and `len` are BYTES, `line` and `col` are 1-based, and `col` counts a
/// multi-byte character as one -- except inside an identifier, where
/// `scan-ident-rest` advances by byte count. That asymmetry is Cobblestone's
/// and is reproduced rather than corrected; a fix belongs upstream, not in a
/// port that has to agree with a gold set.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Token {
    pub kind: Kind,
    pub offset: u32,
    pub len: u32,
    pub line: u32,
    pub col: u32,
}

impl Token {
    pub fn text<'a>(&self, src: &'a [u8]) -> &'a [u8] {
        &src[self.offset as usize..(self.offset + self.len) as usize]
    }
}

/// `lit-text-to-integer` (Token.codex:144). An integer literal's VALUE.
///
/// **`#` IS THE HEX PREFIX, NOT `0x`**, and an underscore is a separator the
/// decimal path skips. The arithmetic is declared `wrapping` upstream, so a
/// literal past the range wraps rather than trapping -- reproduced here, since
/// a panic where upstream wraps is a different program.
///
/// The decimal path subtracts the char-code of `'0'` rather than the byte, but
/// the alphabet numbers `0..9` consecutively, so the digits come out the same;
/// the hex path SKIPS anything that is not a hex digit, which is how it steps
/// over the `#` it starts one past anyway.
pub fn lit_text_to_integer(t: &str) -> i64 {
    let hex_digit = |c: u8| -> Option<i64> {
        match c {
            b'0'..=b'9' => Some((c - b'0') as i64),
            b'a'..=b'f' => Some((c - b'a') as i64 + 10),
            b'A'..=b'F' => Some((c - b'A') as i64 + 10),
            _ => None,
        }
    };
    let b = t.as_bytes();
    if b.first() == Some(&b'#') {
        return b[1..].iter().filter_map(|c| hex_digit(*c)).fold(0i64, |acc, d| {
            acc.wrapping_mul(16).wrapping_add(d)
        });
    }
    b.iter().filter(|c| **c != b'_').fold(0i64, |acc, c| {
        acc.wrapping_mul(10).wrapping_add((c.wrapping_sub(b'0')) as i64)
    })
}

