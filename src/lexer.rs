//! Codex lexing, in Rust.
//!
//! This is not a transcription of `Syntax/Lexer.codex`. Internals are ours;
//! what is owed is the OUTPUT, because a token's kind, byte span and
//! line/column all travel downstream into the IR and into diagnostics that are
//! themselves a gold set. So the rule is narrow: wherever a choice is visible
//! in the token stream, upstream decides it; everywhere else, Rust does.
//!
//! Two consequences worth knowing before changing anything here.
//!
//! **Columns are not byte counts.** Upstream charges one column for a
//! multi-byte character at the start of an identifier and its byte count in
//! the middle of one, so a column drifts inside a non-ASCII name. It is
//! visible in every span, so it is reproduced rather than corrected -- a fix
//! belongs upstream, not in the front end that has to agree with it.
//!
//! **`EndOfFile` sits after trailing spaces**, because upstream's whitespace
//! skip mutates the state the collector later reads. Also visible, also kept.
//!
//! One deliberate addition: this lexer is LOSSLESS. Upstream drops spaces and
//! skipped prose lines on the floor, which is right for a compiler and useless
//! for a linter. We emit `Kind::Spaces` and `Kind::SkippedProse` for them, so
//! every byte lands in exactly one token and the source rebuilds by
//! concatenation. Filter the trivia out and what remains is upstream's stream.

use crate::token::{Kind, Token};

/// A lexer diagnostic. The message text is upstream's verbatim, because
/// `refused.tsv` -- the corpus programs Cobblestone declines -- is a gold set
/// in its own right and we have to reproduce what it says, not merely refuse.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diag {
    pub code: &'static str,
    pub msg: &'static str,
    pub line: u32,
    pub col: u32,
    pub offset: u32,
    pub len: u32,
}

pub struct Lexed {
    pub tokens: Vec<Token>,
    pub errors: Vec<Diag>,
}

impl Lexed {
    /// The projection that must equal `lex.truth`: Cobblestone's stream, with
    /// everything it never saw removed.
    pub fn codex_tokens(&self) -> impl Iterator<Item = &Token> {
        self.tokens.iter().filter(|t| !t.kind.is_trivia())
    }

    /// Losslessness, answered by the source itself and needing no gold set.
    /// Returns the byte offset of the first gap or overlap.
    pub fn lossless_gap(&self, src: &[u8]) -> Option<u32> {
        let mut at = 0u32;
        for t in &self.tokens {
            if t.offset != at {
                return Some(at);
            }
            at += t.len;
        }
        if at as usize != src.len() {
            return Some(at);
        }
        None
    }
}

struct Lexer<'a> {
    src: &'a [u8],
    off: u32,
    line: u32,
    col: u32,
    prose_mode: bool,
    errors: Vec<Diag>,
}

impl<'a> Lexer<'a> {
    fn at_end(&self) -> bool {
        self.off as usize >= self.src.len()
    }

    /// Upstream `peek-code` answers 0 past the end, and several branches lean
    /// on that rather than checking.
    fn peek(&self) -> u8 {
        if self.at_end() {
            0
        } else {
            self.src[self.off as usize]
        }
    }

    fn advance_char(&mut self) {
        if self.peek() == b'\n' {
            self.line += 1;
            self.col = 1;
        } else {
            self.col += 1;
        }
        self.off += 1;
    }

    /// `advance-bytes`: one column for however many bytes. See the module note.
    fn advance_bytes(&mut self, n: u32) {
        self.off += n;
        self.col += 1;
    }

    /// Move to `stop`, charging the column the byte distance. This is the shape
    /// every `scan-*-rest` helper upstream shares.
    fn take_to(&mut self, stop: u32) {
        self.col += stop - self.off;
        self.off = stop;
    }

    fn mark(&self) -> (u32, u32, u32) {
        (self.off, self.line, self.col)
    }

    fn tok(&self, kind: Kind, at: (u32, u32, u32), len: u32) -> Token {
        Token { kind, offset: at.0, len, line: at.1, col: at.2 }
    }
}

// -- character classification ------------------------------------------------
//
// Upstream runs these on `char-code`, which is NOT ASCII (see charcode.rs).
// Every predicate below is nevertheless a faithful equivalent, and each says
// why, because "looks the same" is not an argument at this boundary.

/// `is-letter-code` = `is-letter (code-to-char c)`: it round-trips the code back
/// to the character, so the alphabet's ordering never enters into it.
fn is_letter(b: u8) -> bool {
    b.is_ascii_alphabetic()
}

/// `is-digit-code`, same round trip.
fn is_digit(b: u8) -> bool {
    b.is_ascii_digit()
}

/// `is-tier1-start`: the lead byte of a 2-or-more-byte UTF-8 sequence, tested
/// on the RAW byte rather than a char-code.
fn is_tier1_start(b: u8) -> bool {
    b & 224 == 192
}

fn cce_byte_len(b: u8) -> u32 {
    if b & 128 == 0 {
        1
    } else if b & 224 == 192 {
        2
    } else if b & 240 == 224 {
        3
    } else {
        4
    }
}

fn cce_decode_cp(src: &[u8], off: usize) -> u32 {
    let b0 = src[off] as u32;
    if b0 & 224 == 192 {
        let b1 = *src.get(off + 1).unwrap_or(&0) as u32;
        128 + ((b0 & 31) << 6) + (b1 & 63)
    } else if b0 & 240 == 224 {
        let b1 = *src.get(off + 1).unwrap_or(&0) as u32;
        let b2 = *src.get(off + 2).unwrap_or(&0) as u32;
        2176 + ((b0 & 15) << 12) + ((b1 & 63) << 6) + (b2 & 63)
    } else {
        b0
    }
}

/// Upstream's `is-tier1-letter-cp` answers True for everything under 896 and
/// False above, so it is a RANGE on the encoded value and not a letter test at
/// all. Ported as written.
fn is_tier1_letter_cp(cp: u32) -> bool {
    cp >= 128 && cp - 128 < 896
}

/// `hex-digit-value`. Upstream compares char-codes, but `'0'..'9'` is contiguous
/// in that alphabet too and the letters are tested one at a time by equality,
/// so the accepted SET and the returned VALUE both match this byte version.
fn hex_digit_value(b: u8) -> i32 {
    match b {
        b'0'..=b'9' => (b - b'0') as i32,
        b'a' | b'A' => 10,
        b'b' | b'B' => 11,
        b'c' | b'C' => 12,
        b'd' | b'D' => 13,
        b'e' | b'E' => 14,
        b'f' | b'F' => 15,
        _ => -1,
    }
}

/// `classify-word`. The uppercase arm upstream reads `c >= char-code 'E' &
/// c <= char-code 'Z'`, which is a RANGE over the frequency-ordered alphabet
/// where 'E' is the lowest uppercase code and 'Z' the highest -- so it means
/// "is uppercase" and nothing subtler.
fn classify_word(w: &[u8]) -> Kind {
    match w {
        b"let" => Kind::LetKeyword,
        b"in" => Kind::InKeyword,
        b"between" => Kind::BetweenKeyword,
        b"and" => Kind::AndKeyword,
        b"or" => Kind::OrKeyword,
        b"xor" => Kind::XorKeyword,
        b"not" => Kind::NotKeyword,
        b"if" => Kind::IfKeyword,
        b"is" => Kind::IsKeyword,
        b"otherwise" => Kind::OtherwiseKeyword,
        b"then" => Kind::ThenKeyword,
        b"else" => Kind::ElseKeyword,
        b"when" => Kind::WhenKeyword,
        b"where" => Kind::WhereKeyword,
        b"act" => Kind::ActKeyword,
        b"end" => Kind::EndKeyword,
        b"record" => Kind::RecordKeyword,
        b"cites" => Kind::CitesKeyword,
        b"grounds" => Kind::GroundsKeyword,
        b"quotes" => Kind::QuotesKeyword,
        b"trusting" => Kind::TrustingKeyword,
        b"above" => Kind::AboveKeyword,
        b"claim" => Kind::ClaimKeyword,
        b"proof" => Kind::ProofKeyword,
        b"qed" => Kind::QedKeyword,
        b"induction" => Kind::InductionKeyword,
        b"forall" => Kind::ForAllKeyword,
        b"exists" => Kind::ThereExistsKeyword,
        b"linear" => Kind::LinearKeyword,
        b"mutable" => Kind::MutableKeyword,
        b"punctual" => Kind::PunctualKeyword,
        b"bounded" => Kind::BoundedKeyword,
        b"unit" => Kind::UnitKeyword,
        b"effect" => Kind::EffectKeyword,
        b"class" => Kind::ClassKeyword,
        b"instance" => Kind::InstanceKeyword,
        b"with" => Kind::WithKeyword,
        b"with-timeout" => Kind::WithTimeoutKeyword,
        b"trying" => Kind::TryingKeyword,
        b"lazy" => Kind::LazyKeyword,
        b"revised" => Kind::RevisedKeyword,
        b"True" => Kind::TrueKeyword,
        b"False" => Kind::FalseKeyword,
        _ => {
            if w.first().copied().is_some_and(|c| c.is_ascii_uppercase()) {
                Kind::TypeIdentifier
            } else {
                Kind::Identifier
            }
        }
    }
}

// -- scanners over the raw source -------------------------------------------

fn skip_spaces_end(src: &[u8], mut off: u32) -> u32 {
    while (off as usize) < src.len() && src[off as usize] == b' ' {
        off += 1;
    }
    off
}

fn scan_to_eol_end(src: &[u8], mut off: u32) -> u32 {
    while (off as usize) < src.len() && src[off as usize] != b'\n' {
        off += 1;
    }
    off
}

/// The hyphen rule, upstream's own words: *"The minus binds to whatever it
/// abuts... `a-2` and `a-b` are one name, and so is `a-`. A hyphen with a space
/// before it is not reached here at all."* A `->` ends the name.
fn scan_ident_end(src: &[u8], mut off: u32) -> u32 {
    let len = src.len() as u32;
    while off < len {
        let c = src[off as usize];
        if is_letter(c) || is_digit(c) || c == b'_' {
            off += 1;
        } else if is_tier1_start(c) {
            let cp = cce_decode_cp(src, off as usize);
            if is_tier1_letter_cp(cp) {
                off += cce_byte_len(c);
            } else {
                return off;
            }
        } else if c == b'-' {
            if off + 1 >= len {
                return off + 1;
            } else if src[(off + 1) as usize] == b'>' {
                return off;
            } else {
                off += 1;
            }
        } else {
            return off;
        }
    }
    off
}

fn scan_digits_end(src: &[u8], mut off: u32) -> u32 {
    let len = src.len() as u32;
    while off < len {
        let c = src[off as usize];
        if is_digit(c) || c == b'_' {
            off += 1;
        } else {
            return off;
        }
    }
    off
}

fn scan_hex_end(src: &[u8], mut off: u32) -> u32 {
    let len = src.len() as u32;
    while off < len {
        let c = src[off as usize];
        if hex_digit_value(c) >= 0 || c == b'_' {
            off += 1;
        } else {
            return off;
        }
    }
    off
}

/// A backslash consumes the next byte whatever it is, which is how an escaped
/// quote stays inside the literal.
fn scan_string_end(src: &[u8], mut off: u32) -> u32 {
    let len = src.len() as u32;
    while off < len {
        match src[off as usize] {
            b'"' => return off + 1,
            b'\n' => return off,
            b'\\' => off += 2,
            _ => off += 1,
        }
    }
    off
}

// -- the driver --------------------------------------------------------------

pub fn tokenize(src: &[u8]) -> Lexed {
    tokenize_into(src, false)
}

pub fn tokenize_into(src: &[u8], prose_mode: bool) -> Lexed {
    let mut lx = Lexer { src, off: 0, line: 1, col: 1, prose_mode, errors: Vec::new() };
    // Cobblestone's own subject runs ~5,300 tokens over 27 KB. One token per
    // four bytes is a shape, not a measurement, and only saves regrowth.
    let mut out: Vec<Token> = Vec::with_capacity(src.len() / 4 + 16);

    loop {
        // skip-spaces, but recorded. Upstream returns the same mutated state,
        // which is why EndOfFile below sits AFTER the trailing spaces.
        let sp = lx.mark();
        let stop = skip_spaces_end(src, lx.off);
        if stop != lx.off {
            lx.take_to(stop);
            out.push(lx.tok(Kind::Spaces, sp, stop - sp.0));
        }

        if lx.at_end() {
            let at = lx.mark();
            out.push(lx.tok(Kind::EndOfFile, at, 0));
            break;
        }

        let at = lx.mark();
        let c = lx.peek();

        // Upstream's first branch is `if c == cc-cr`, and `cc-cr` is bound to
        // -1 -- a value no byte can equal -- so that arm is unreachable. A
        // carriage return therefore falls through to scan-operator and lexes
        // as ErrorToken. That is consistent with CCE, which rejects `\r`
        // outright; it is not an oversight to be repaired here.

        // Column 2 means exactly one leading space, which is how a prose line
        // is marked. Off prose mode the line is consumed and never recorded --
        // we record it as trivia so the file can be rebuilt.
        if lx.col == 2 && c != b'\n' {
            let stop = scan_to_eol_end(src, lx.off);
            lx.take_to(stop);
            let kind = if lx.prose_mode { Kind::ProseText } else { Kind::SkippedProse };
            out.push(lx.tok(kind, at, stop - at.0));
            continue;
        }

        if c == b'\n' {
            lx.advance_char();
            out.push(lx.tok(Kind::Newline, at, 1));
            continue;
        }

        if c == b'"' {
            lx.advance_char();
            let entry = lx.off;
            let stop = scan_string_end(src, lx.off);
            lx.take_to(stop);
            let terminated = stop <= src.len() as u32
                && stop > entry
                && src[(stop - 1) as usize] == b'"';
            if !terminated {
                // The span upstream builds points at the opening quote.
                lx.errors.push(Diag {
                    code: "cdx-unterminated-text",
                    msg: "Unterminated text literal: hit end of line before closing '\"'",
                    line: at.1,
                    col: at.2,
                    offset: at.0,
                    len: 1,
                });
            }
            out.push(lx.tok(Kind::TextLiteral, at, lx.off - at.0));
            continue;
        }

        if c == b'\'' {
            scan_char_literal(&mut lx, &mut out, at);
            continue;
        }

        if is_letter(c) {
            lx.advance_char();
            let stop = scan_ident_end(src, lx.off);
            lx.take_to(stop);
            let word = &src[at.0 as usize..lx.off as usize];
            out.push(lx.tok(classify_word(word), at, lx.off - at.0));
            continue;
        }

        if is_tier1_start(c) {
            let cp = cce_decode_cp(src, lx.off as usize);
            if is_tier1_letter_cp(cp) {
                lx.advance_bytes(cce_byte_len(c));
                let stop = scan_ident_end(src, lx.off);
                lx.take_to(stop);
                // Never a keyword and never a TypeIdentifier: upstream does not
                // run classify-word on this path at all.
                out.push(lx.tok(Kind::Identifier, at, lx.off - at.0));
            } else {
                lx.advance_char();
                out.push(lx.tok(Kind::ErrorToken, at, 1));
            }
            continue;
        }

        if c == b'_' {
            lx.advance_char();
            let stop = scan_ident_end(src, lx.off);
            lx.take_to(stop);
            let len = lx.off - at.0;
            let kind = if len == 1 {
                Kind::Underscore
            } else {
                classify_word(&src[at.0 as usize..lx.off as usize])
            };
            out.push(lx.tok(kind, at, len));
            continue;
        }

        if is_digit(c) {
            scan_number(&mut lx, &mut out, at);
            continue;
        }

        if c == b'#' {
            lx.advance_char();
            let stop = scan_hex_end(src, lx.off);
            lx.take_to(stop);
            // `#` with no hex digit after it is one bad byte, not a literal.
            let kind = if lx.off - at.0 == 1 { Kind::ErrorToken } else { Kind::IntegerLiteral };
            out.push(lx.tok(kind, at, lx.off - at.0));
            continue;
        }

        scan_operator(&mut lx, &mut out, at);
    }

    Lexed { tokens: out, errors: lx.errors }
}

/// `1.` and `1..2` both keep the dot for the parser; only `1.5` is a Number.
fn scan_number(lx: &mut Lexer, out: &mut Vec<Token>, at: (u32, u32, u32)) {
    lx.advance_char();
    let stop = scan_digits_end(lx.src, lx.off);
    lx.take_to(stop);
    let int_end = lx.off;
    if lx.at_end() || lx.peek() != b'.' {
        out.push(lx.tok(Kind::IntegerLiteral, at, int_end - at.0));
        return;
    }
    // Look past the dot without committing to it.
    let after_dot = lx.off + 1;
    if after_dot as usize >= lx.src.len() || lx.src[after_dot as usize] == b'.' {
        out.push(lx.tok(Kind::IntegerLiteral, at, int_end - at.0));
        return;
    }
    lx.advance_char();
    let stop = scan_digits_end(lx.src, lx.off);
    lx.take_to(stop);
    out.push(lx.tok(Kind::NumberLiteral, at, lx.off - at.0));
}

fn scan_char_literal(lx: &mut Lexer, out: &mut Vec<Token>, at: (u32, u32, u32)) {
    lx.advance_char(); // past the opening quote
    if lx.at_end() {
        out.push(lx.tok(Kind::ErrorToken, at, lx.off - at.0));
        return;
    }
    if lx.peek() == b'\\' {
        let esc_at = lx.mark();
        lx.advance_char();
        if lx.at_end() {
            out.push(lx.tok(Kind::ErrorToken, at, lx.off - at.0));
            return;
        }
        let esc = lx.peek();
        lx.advance_char();
        if !lx.at_end() && lx.peek() == b'\'' {
            lx.advance_char();
        }
        // CCE has no tab and no carriage return, and says so by code.
        let refusal = match esc {
            b't' => Some((
                "cdx-invalid-tab-escape",
                "\\t escape is not valid in CCE; use a space character instead",
            )),
            b'r' => Some((
                "cdx-invalid-carriage-return-escape",
                "\\r escape is not valid in CCE; use '\\n' for newlines",
            )),
            _ => None,
        };
        if let Some((code, msg)) = refusal {
            lx.errors.push(Diag {
                code,
                msg,
                line: esc_at.1,
                col: esc_at.2,
                offset: esc_at.0,
                len: 2,
            });
        }
        out.push(lx.tok(Kind::CharLiteral, at, lx.off - at.0));
        return;
    }
    lx.advance_char();
    if !lx.at_end() && lx.peek() == b'\'' {
        lx.advance_char();
    }
    out.push(lx.tok(Kind::CharLiteral, at, lx.off - at.0));
}

fn scan_operator(lx: &mut Lexer, out: &mut Vec<Token>, at: (u32, u32, u32)) {
    let c = lx.peek();
    let nc = if (lx.off + 1) as usize >= lx.src.len() {
        0
    } else {
        lx.src[(lx.off + 1) as usize]
    };
    let nc2 = if (lx.off + 2) as usize >= lx.src.len() {
        0
    } else {
        lx.src[(lx.off + 2) as usize]
    };

    let (kind, len): (Kind, u32) = match c {
        b'(' => (Kind::LeftParen, 1),
        b')' => (Kind::RightParen, 1),
        b'[' => (Kind::LeftBracket, 1),
        b']' => (Kind::RightBracket, 1),
        b'{' => (Kind::LeftBrace, 1),
        b'}' => (Kind::RightBrace, 1),
        b',' => (Kind::Comma, 1),
        b'.' => (Kind::Dot, 1),
        b'^' => (Kind::Caret, 1),
        b'&' => (Kind::Ampersand, 1),
        b'\\' => (Kind::Backslash, 1),
        b'~' if nc == b'0' => (Kind::TildeZero, 2),
        b'~' => (Kind::Tilde, 1),
        b'+' => (Kind::Plus, 1),
        b'-' if nc == b'>' => (Kind::Arrow, 2),
        b'-' => (Kind::Minus, 1),
        b'*' => (Kind::Star, 1),
        b'/' if nc == b'=' => (Kind::NotEquals, 2),
        b'/' => (Kind::Slash, 1),
        b'=' if nc == b'=' && nc2 == b'=' => (Kind::TripleEquals, 3),
        b'=' if nc == b'=' => (Kind::DoubleEquals, 2),
        b'=' if nc == b'>' => (Kind::FatArrow, 2),
        b'=' => (Kind::Equals, 1),
        b':' if nc == b':' => (Kind::ColonColon, 2),
        b':' => (Kind::Colon, 1),
        b'|' if nc == b'>' => (Kind::PipeForward, 2),
        b'|' => (Kind::Pipe, 1),
        b'<' if nc == b'=' => (Kind::LessOrEqual, 2),
        b'<' if nc == b'-' => (Kind::LeftArrow, 2),
        b'<' => (Kind::LessThan, 1),
        b'>' if nc == b'=' => (Kind::GreaterOrEqual, 2),
        b'>' => (Kind::GreaterThan, 1),
        _ => (Kind::ErrorToken, 1),
    };
    for _ in 0..len {
        lx.advance_char();
    }
    out.push(lx.tok(kind, at, len));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(src: &str) -> Vec<Kind> {
        tokenize(src.as_bytes()).codex_tokens().map(|t| t.kind).collect()
    }

    fn lossless(src: &str) {
        let lexed = tokenize(src.as_bytes());
        assert_eq!(lexed.lossless_gap(src.as_bytes()), None, "not lossless: {src:?}");
    }

    #[test]
    fn a_hyphen_binds_to_what_it_abuts() {
        // Upstream's rule, and the reason `a - 2` and `a-2` are different
        // things: the scan stops at a space, so a hyphen is only ever part of
        // a name when it touches the character before it.
        // Indented, because at the left margin a one-character token would put
        // the next character in column 2 and turn the rest of the line into
        // prose. See `column_two_after_a_short_token_is_still_prose`.
        assert_eq!(kinds("  a-b"), vec![Kind::Identifier, Kind::EndOfFile]);
        assert_eq!(kinds("  a-2"), vec![Kind::Identifier, Kind::EndOfFile]);
        assert_eq!(kinds("  a-"), vec![Kind::Identifier, Kind::EndOfFile]);
        assert_eq!(
            kinds("  a - 2"),
            vec![Kind::Identifier, Kind::Minus, Kind::IntegerLiteral, Kind::EndOfFile]
        );
        // `->` ends a name rather than continuing it, or every signature would
        // lex as one identifier.
        assert_eq!(
            kinds("  a->b"),
            vec![Kind::Identifier, Kind::Arrow, Kind::Identifier, Kind::EndOfFile]
        );
    }

    #[test]
    fn exactly_one_leading_space_means_prose() {
        // Column 2 is the marker. Two spaces is code, one space is prose, and
        // the prose line is trivia here where upstream simply loses it.
        assert_eq!(kinds("  let"), vec![Kind::LetKeyword, Kind::EndOfFile]);
        assert_eq!(kinds(" let"), vec![Kind::EndOfFile]);
        let lexed = tokenize(b" prose here\n  let");
        assert_eq!(lexed.tokens[1].kind, Kind::SkippedProse);
        lossless(" prose here\n  let");
    }

    #[test]
    fn uppercase_is_a_type_identifier_from_a_not_from_e() {
        // The regression guard for the char-code misreading: upstream's range
        // test is over a frequency-ordered alphabet where 'E' is the LOWEST
        // uppercase code, so it means "is uppercase" and A-D are included.
        for w in ["Alpha", "Boolean", "Chapter", "Diagnostic", "Zed"] {
            assert_eq!(kinds(w), vec![Kind::TypeIdentifier, Kind::EndOfFile], "{w}");
        }
        assert_eq!(kinds("alpha"), vec![Kind::Identifier, Kind::EndOfFile]);
    }

    #[test]
    fn a_dot_only_makes_a_number_when_a_digit_follows() {
        assert_eq!(kinds("  1.5"), vec![Kind::NumberLiteral, Kind::EndOfFile]);
        assert_eq!(kinds("  1."), vec![Kind::IntegerLiteral, Kind::Dot, Kind::EndOfFile]);
        assert_eq!(
            kinds("  1..2"),
            vec![Kind::IntegerLiteral, Kind::Dot, Kind::Dot, Kind::IntegerLiteral, Kind::EndOfFile]
        );
    }

    #[test]
    fn a_text_literal_open_at_end_of_line_is_refused() {
        // PR 114. The old lexer returned early on the one input that produces
        // an empty scan, so `"` at end of line emitted an empty literal and
        // reported nothing.
        let lexed = tokenize(b"x = \"\n");
        assert_eq!(lexed.errors.len(), 1);
        assert_eq!(lexed.errors[0].code, "cdx-unterminated-text");
        assert_eq!(kinds("x = \"\n"),
                   vec![Kind::Identifier, Kind::Equals, Kind::TextLiteral,
                        Kind::Newline, Kind::EndOfFile]);
    }

    #[test]
    fn an_escaped_quote_stays_inside_the_literal() {
        assert_eq!(kinds(r#""a\"b""#), vec![Kind::TextLiteral, Kind::EndOfFile]);
        assert!(tokenize(br#""a\"b""#).errors.is_empty());
    }

    #[test]
    fn cce_refuses_the_tab_and_carriage_return_escapes() {
        assert_eq!(tokenize(b"'\\t'").errors[0].code, "cdx-invalid-tab-escape");
        assert_eq!(tokenize(b"'\\r'").errors[0].code,
                   "cdx-invalid-carriage-return-escape");
        assert!(tokenize(b"'\\n'").errors.is_empty());
    }

    #[test]
    fn every_byte_is_accounted_for() {
        for src in [
            "",
            "\n",
            "   ",
            "  x = 1\n\n  y = \"two\"\n",
            " prose\n  code\n prose\n",
            "  f (a) (b) = a-b\n",
            "  h : Integer = #ff\n",
            "  bad = #\n",
        ] {
            lossless(src);
        }
    }

    #[test]
    fn column_two_after_a_short_token_is_still_prose() {
        // The prose rule is not "one leading space", it is "column 2", and the
        // column does not care how it got there. A single-character token at
        // the left margin therefore swallows the rest of its own line. Real
        // Codex indents its code by two, so this is a trap for hand-written
        // test inputs rather than for real source -- but it is upstream's
        // behaviour, and a port that quietly special-cased line starts would
        // disagree with the golds on any file that does it.
        assert_eq!(kinds("a->b"), vec![Kind::Identifier, Kind::EndOfFile]);
        let lexed = tokenize(b"a->b");
        assert_eq!(lexed.tokens[1].kind, Kind::SkippedProse);
        assert_eq!(lexed.tokens[1].text(b"a->b"), b"->b");
        lossless("a->b");
    }

    #[test]
    fn end_of_file_lands_after_trailing_spaces() {
        // Upstream's whitespace skip mutates the state the collector reads, so
        // the marker is at the end of the file rather than before the spaces.
        let lexed = tokenize(b"x   ");
        let eof = lexed.tokens.last().unwrap();
        assert_eq!(eof.kind, Kind::EndOfFile);
        assert_eq!((eof.offset, eof.len, eof.col), (4, 0, 5));
    }
}
