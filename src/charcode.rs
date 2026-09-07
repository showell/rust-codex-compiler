// Codex `char-code`, measured from the compiler by ladder charcode_probe.py.
// NOT ASCII: a frequency-ordered private alphabet, 1..96. 0 means the byte
// has no code. See that script for why this cannot be transcribed by hand.
pub const CHAR_CODE: [u8; 128] = [
    0, //   0 (not in the alphabet)
    0, //   1 (not in the alphabet)
    0, //   2 (not in the alphabet)
    0, //   3 (not in the alphabet)
    0, //   4 (not in the alphabet)
    0, //   5 (not in the alphabet)
    0, //   6 (not in the alphabet)
    0, //   7 (not in the alphabet)
    0, //   8 (not in the alphabet)
    0, //   9 (not in the alphabet)
    1, //  10 '\n'
    0, //  11 (not in the alphabet)
    0, //  12 (not in the alphabet)
    0, //  13 (not in the alphabet)
    0, //  14 (not in the alphabet)
    0, //  15 (not in the alphabet)
    0, //  16 (not in the alphabet)
    0, //  17 (not in the alphabet)
    0, //  18 (not in the alphabet)
    0, //  19 (not in the alphabet)
    0, //  20 (not in the alphabet)
    0, //  21 (not in the alphabet)
    0, //  22 (not in the alphabet)
    0, //  23 (not in the alphabet)
    0, //  24 (not in the alphabet)
    0, //  25 (not in the alphabet)
    0, //  26 (not in the alphabet)
    0, //  27 (not in the alphabet)
    0, //  28 (not in the alphabet)
    0, //  29 (not in the alphabet)
    0, //  30 (not in the alphabet)
    0, //  31 (not in the alphabet)
    2, //  32 ' '
    67, //  33 '!'
    72, //  34 '"'
    83, //  35 '#'
    95, //  36 '$'
    96, //  37 '%'
    84, //  38 '&'
    71, //  39 "'"
    74, //  40 '('
    75, //  41 ')'
    78, //  42 '*'
    76, //  43 '+'
    66, //  44 ','
    73, //  45 '-'
    65, //  46 '.'
    81, //  47 '/'
    3, //  48 '0'
    4, //  49 '1'
    5, //  50 '2'
    6, //  51 '3'
    7, //  52 '4'
    8, //  53 '5'
    9, //  54 '6'
    10, //  55 '7'
    11, //  56 '8'
    12, //  57 '9'
    69, //  58 ':'
    70, //  59 ';'
    79, //  60 '<'
    77, //  61 '='
    80, //  62 '>'
    68, //  63 '?'
    82, //  64 '@'
    41, //  65 'A'
    58, //  66 'B'
    50, //  67 'C'
    48, //  68 'D'
    39, //  69 'E'
    54, //  70 'F'
    55, //  71 'G'
    46, //  72 'H'
    43, //  73 'I'
    61, //  74 'J'
    60, //  75 'K'
    49, //  76 'L'
    52, //  77 'M'
    44, //  78 'N'
    42, //  79 'O'
    57, //  80 'P'
    63, //  81 'Q'
    47, //  82 'R'
    45, //  83 'S'
    40, //  84 'T'
    51, //  85 'U'
    59, //  86 'V'
    53, //  87 'W'
    62, //  88 'X'
    56, //  89 'Y'
    64, //  90 'Z'
    88, //  91 '['
    86, //  92 '\\'
    89, //  93 ']'
    94, //  94 '^'
    85, //  95 '_'
    93, //  96 '`'
    15, //  97 'a'
    32, //  98 'b'
    24, //  99 'c'
    22, // 100 'd'
    13, // 101 'e'
    28, // 102 'f'
    29, // 103 'g'
    20, // 104 'h'
    17, // 105 'i'
    35, // 106 'j'
    34, // 107 'k'
    23, // 108 'l'
    26, // 109 'm'
    18, // 110 'n'
    16, // 111 'o'
    31, // 112 'p'
    37, // 113 'q'
    21, // 114 'r'
    19, // 115 's'
    14, // 116 't'
    25, // 117 'u'
    33, // 118 'v'
    27, // 119 'w'
    36, // 120 'x'
    30, // 121 'y'
    38, // 122 'z'
    90, // 123 '{'
    87, // 124 '|'
    91, // 125 '}'
    92, // 126 '~'
    0, // 127 (not in the alphabet)
];

/// CCE codes 97..=127, the half of the alphabet that is not ASCII.
///
/// **DERIVED FROM THE COMPILER, like the table above, and for a sharper
/// reason.** `CHAR_CODE` is indexed by BYTE and so can only ever describe the
/// 128 codes a byte can reach. The alphabet does not stop there: 97..=112 are
/// accented Latin and 113..=127 are Cyrillic, and a program that names them
/// says so out loud -- `vbe-mode-set` carries the section title
/// `"Accented(CCE 97-112->approx glyphs)" "Cyrillic(CCE 113-127->...)"`.
///
/// Without this, `code-to-char` fell through `unwrap_or('\0')` and answered NUL
/// for every one of them. Ten corpus programs emitted IR that was byte-for-byte
/// right except for a run of NULs where the oracle had Cyrillic, and every one
/// of them differed from the oracle by exactly 61 bytes -- the same silent
/// fallback wearing ten different sizes.
///
/// **THE ALPHABET ENDS AT 127.** Probing the compiler past it answers U+FFFD,
/// and at 233 a clapping-hands emoji: that is the native binary reading off the
/// end of its own table, not a mapping, so nothing here extends beyond 127.
pub const CHAR_CODE_HIGH: [char; 31] = [
    'é', 'è', 'ê', 'ë', 'á', 'à', 'â', 'ä', // 97..104
    'ó', 'ô', 'ö', 'ú', 'ü', 'ñ', 'ç', 'í', // 105..112
    'а', 'о', 'е', 'и', 'н', 'т', 'с', 'р', // 113..120
    'в', 'л', 'к', 'м', 'д', 'п', 'у', // 121..127
];

/// The lowest code `CHAR_CODE_HIGH` describes.
pub const HIGH_BASE: i64 = 97;



/// `char-code`: the code the alphabet gives this character, or 0.
pub fn char_code(c: char) -> i64 {
    if (c as u32) < CHAR_CODE.len() as u32 {
        return CHAR_CODE[c as usize] as i64;
    }
    CHAR_CODE_HIGH
        .iter()
        .position(|h| *h == c)
        .map(|i| HIGH_BASE + i as i64)
        .unwrap_or(0)
}

/// The character a code names, or NUL when the alphabet does not name one.
///
/// The NUL is still here and is still a real answer -- code 0 is "not in the
/// alphabet" and the compiler answers nothing for it either. What changed is
/// that it is no longer reached by codes 97..=127, which ARE in the alphabet
/// and used to fall through to it.

/// `code-to-char`: the character a code names, or NUL where the alphabet
/// names none.
pub fn code_to_char(code: i64) -> char {
    if (HIGH_BASE..HIGH_BASE
        + CHAR_CODE_HIGH.len() as i64)
        .contains(&code)
    {
        return CHAR_CODE_HIGH[(code - HIGH_BASE) as usize];
    }
    CHAR_CODE
        .iter()
        .position(|c| *c as i64 == code && code != 0)
        .map(|b| b as u8 as char)
        .unwrap_or('\0')
}

/// A char literal's VALUE, which is its char-code and not its byte --
/// `decode-char-literal-value` (Desugarer.codex:96).
///
/// The desugarer decodes a char literal where it decodes a text one, so by the
/// time anything downstream sees `ALitExpr` the token `'a'` has become the
/// text `"15"`. Ours keeps the raw token, so the decode happens here instead.
///
/// **`\t` IS ONE SPACE AND `\r` IS A NEWLINE HERE**, and that is NOT what the
/// same two escapes mean inside a TEXT literal, where `lexer::decode_escapes`
/// gives `\t` two spaces and drops `\r` entirely. The two decoders are
/// genuinely different upstream -- this one is `decode-char-literal-value` in
/// `Ast/Desugarer.codex`, that one is `decode-escapes` in `Syntax/Lexer.codex`
/// -- so they are written apart rather than shared.
///
/// Anything else after a backslash is its own char-code, so `\q` is `q`.
pub fn char_literal_code(raw: &str) -> i64 {
    let body = raw.strip_prefix('\'').map_or(raw, |s| s.strip_suffix('\'').unwrap_or(s));
    let b = body.as_bytes();
    if b.is_empty() {
        return 0;
    }
    let code = |c: u8| -> i64 { CHAR_CODE.get(c as usize).copied().unwrap_or(0) as i64 };
    let c0 = code(b[0]);
    if c0 != code(b'\\') || b.len() < 2 {
        return c0;
    }
    let nc = code(b[1]);
    if nc == code(b'n') || nc == code(b'r') {
        code(b'\n')
    } else if nc == code(b't') {
        code(b' ')
    } else {
        nc
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **EVERY PAIR READ OFF THE COMPILER**, by transpiling a program that
    /// prints `char-to-text (code-to-char i)` for each code and running the
    /// binary. Not transcribed from the section title that names the ranges:
    /// that title says "Accented(CCE 97-112)" and "Cyrillic(CCE 113-127)" and
    /// says nothing about WHICH accented letters, or their order.
    #[test]
    fn the_alphabet_does_not_stop_at_ascii() {
        assert_eq!(CHAR_CODE_HIGH.len(), 31, "97..=127 is thirty-one codes");
        assert_eq!(CHAR_CODE_HIGH[0], 'é');
        assert_eq!(CHAR_CODE_HIGH[15], 'í'); // 112, the last accented one
        assert_eq!(CHAR_CODE_HIGH[16], 'а'); // 113, the first Cyrillic one
        assert_eq!(CHAR_CODE_HIGH[30], 'у'); // 127, the last code there is
        // The two halves do not overlap: an accented letter is Latin-1 and a
        // Cyrillic one is not, which is what makes the boundary checkable.
        assert!(CHAR_CODE_HIGH[..16].iter().all(|c| (*c as u32) < 0x100));
        assert!(CHAR_CODE_HIGH[16..].iter().all(|c| (0x400..0x460).contains(&(*c as u32))));
    }
}
