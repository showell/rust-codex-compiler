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
}

impl Kind {
    /// Is this ours rather than Cobblestone's? Filtering these out is exactly
    /// the projection that must equal `lex.truth`.
    pub fn is_trivia(self) -> bool {
        matches!(self, Kind::Spaces | Kind::SkippedProse)
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
