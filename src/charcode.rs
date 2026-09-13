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

// ---- units: framing, printing, reading --------------------------------------
//
// A Codex Text is a sequence of CCE UNITS, 0..=255. A code 0..=127 is one
// unit; a code point outside the alphabet is FRAMED as 2, 3 or 4 units with
// bands at 128, 2176 and 67712 (`cce-encode-into`, Foreword CCE). The tables
// and conversions below are the zig plug's prelude parts, which Steve named as
// the template; printing and file reading follow x86, which the verdicts were
// captured on, where the two differ.

/// The code point a code 0..=127 names: the zig prelude's `cce_table`.
pub fn tier0_point(code: u8) -> u32 {
    if code == 0 { 0 } else { code_to_char(code as i64) as u32 }
}

/// Tier 1, codes 128..=2175: `cce_t1_code`, `cce_t1_size`, `cce_t1_uni`.
const T1_CODE: [u32; 11] = [128, 384, 512, 640, 768, 896, 1024, 1152, 1280, 1792, 2048];
const T1_SIZE: [u32; 11] = [256, 128, 128, 128, 128, 128, 128, 128, 512, 256, 128];
const T1_UNI: [u32; 11] = [128, 1024, 880, 1536, 1424, 2304, 3584, 4352, 19968, 12352, 8704];
/// Tier 2, codes from 2176, cumulative: `cce_t2_uni`, `cce_t2_size`.
const T2_UNI: [u32; 10] = [12288, 12352, 12448, 19968, 13312, 44032, 3584, 8192, 127744, 9728];
const T2_SIZE: [u32; 10] = [64, 96, 96, 20992, 6592, 11172, 256, 512, 1024, 256];

/// `cx_cp_to_cce`: the code for a code point, tier 0 first. A code point no
/// tier covers is `?`, code 68, as bare metal substitutes it.
pub fn code_of_point(cp: u32) -> u32 {
    if let Some(code) = (0..128u8).find(|c| tier0_point(*c) == cp) {
        return code as u32;
    }
    for ((start, size), uni) in T1_CODE.iter().zip(T1_SIZE).zip(T1_UNI) {
        if cp >= uni && cp < uni + size {
            return start + (cp - uni);
        }
    }
    let mut base = 2176;
    for (uni, size) in T2_UNI.iter().zip(T2_SIZE) {
        if cp >= *uni && cp < uni + size {
            return base + (cp - uni);
        }
        base += size;
    }
    68
}

/// `cx_cce_frame`: a code as 1..=4 units.
pub fn frame(code: u32, out: &mut Vec<u8>) {
    if code < 128 {
        out.push(code as u8);
    } else if code < 2176 {
        let v = code - 128;
        out.extend([(192 + (v >> 6)) as u8, (128 + (v & 63)) as u8]);
    } else if code < 67712 {
        let v = code - 2176;
        out.extend([(224 + (v >> 12)) as u8, (128 + ((v >> 6) & 63)) as u8, (128 + (v & 63)) as u8]);
    } else {
        let v = code - 67712;
        out.extend([
            (240 + (v >> 18)) as u8,
            (128 + ((v >> 12) & 63)) as u8,
            (128 + ((v >> 6) & 63)) as u8,
            (128 + (v & 63)) as u8,
        ]);
    }
}

/// A Rust string as the units a Codex literal holds: every character through
/// `code_of_point`, framed.
pub fn units_of(s: &str) -> Vec<u8> {
    let mut out = Vec::with_capacity(s.len());
    for c in s.chars() {
        frame(code_of_point(c as u32), &mut out);
    }
    out
}

/// x86's `tier1-slice-bases`: the code point starting each 128-code slice of
/// tier 1, indexed by `(code - 128) >> 7`. **Slice 0 starts at U+00C0 where
/// the encoding's tier 1 starts at U+0080**, so codes 128..=383 print 64 code
/// points above the character that framed them. That is x86's table, emulated.
const X86_T1_BASES: [u64; 16] =
    [192, 320, 1024, 880, 1536, 1424, 2304, 3584, 4352, 19968, 20096, 20224, 20352, 12352, 12480, 8704];

/// x86's `tier2-rodata`: per slice, the code it ends before (two bytes) and
/// the delta to its code point (four bytes, added unsigned in a 64-bit
/// register).
const X86_T2: [[u8; 6]; 10] = [
    [192, 8, 128, 39, 0, 0],
    [32, 9, 128, 39, 0, 0],
    [128, 9, 128, 39, 0, 0],
    [128, 91, 128, 68, 0, 0],
    [64, 117, 128, 216, 255, 255],
    [228, 160, 192, 54, 0, 0],
    [228, 161, 28, 109, 255, 255],
    [228, 163, 28, 126, 255, 255],
    [228, 167, 28, 79, 1, 0],
    [228, 168, 28, 126, 255, 255],
];

/// **What x86's print loop writes for these units** (`emit-print-text-loop`,
/// `__cce_print_multi`, `emit-cce-utf8-output`), byte for byte.
///
/// A unit below 128 is its tier-0 code point, in one byte or two. A unit whose
/// top nibble is 1110 starts a 3-unit tier-2 frame, found by scanning the
/// slice table, U+FFFD when none holds it, written as 3 bytes below 65536 and
/// 4 above. Every other unit from 128 is taken as a 2-unit tier-1 frame,
/// continuations and 4-unit leads included. Each byte is the low byte of the
/// shifted value, as the register writes it; a unit past the end reads as 0.
pub fn print_bytes(units: &[u8], out: &mut Vec<u8>) {
    let at = |k: usize| units.get(k).copied().unwrap_or(0) as u64;
    let mut i = 0;
    while i < units.len() {
        let b0 = units[i] as u64;
        if b0 < 128 {
            let cp = tier0_point(b0 as u8) as u64;
            if cp < 128 {
                out.push(cp as u8);
            } else {
                out.extend([((cp >> 6) | 192) as u8, ((cp & 63) | 128) as u8]);
            }
            i += 1;
        } else if b0 & 240 == 224 {
            let code = 2176 + ((b0 & 15) << 12) + ((at(i + 1) & 63) << 6) + (at(i + 2) & 63);
            let cp = X86_T2
                .iter()
                .find(|e| code < (e[0] as u64 | (e[1] as u64) << 8))
                .map_or(65533, |e| code + u32::from_le_bytes([e[2], e[3], e[4], e[5]]) as u64);
            if cp < 65536 {
                out.extend([((cp >> 12) | 224) as u8, (((cp >> 6) & 63) | 128) as u8, ((cp & 63) | 128) as u8]);
            } else {
                out.extend([
                    ((cp >> 18) | 240) as u8,
                    (((cp >> 12) & 63) | 128) as u8,
                    (((cp >> 6) & 63) | 128) as u8,
                    ((cp & 63) | 128) as u8,
                ]);
            }
            i += 3;
        } else {
            let v = ((b0 & 31) << 6) + (at(i + 1) & 63);
            let cp = X86_T1_BASES[(v >> 7) as usize] + (v & 127);
            if cp < 128 {
                out.push(cp as u8);
            } else if cp < 2048 {
                out.extend([((cp >> 6) | 192) as u8, ((cp & 63) | 128) as u8]);
            } else {
                out.extend([((cp >> 12) | 224) as u8, (((cp >> 6) & 63) | 128) as u8, ((cp & 63) | 128) as u8]);
            }
            i += 2;
        }
    }
}

/// **What x86's `read-file-uni` makes of a file's bytes.** A byte below 128
/// is the code the alphabet gives it (`?` where it gives none), a carriage
/// return is dropped, NUL or EOT ends the text, and a byte from 128 is kept
/// raw -- the compiler frames it later, in `utf8-to-cce`.
pub fn read_file_units(bytes: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(bytes.len());
    for &b in bytes {
        match b {
            0 | 4 => break,
            13 => {}
            b if b < 128 => out.push(code_of_point(b as u32) as u8),
            b => out.push(b),
        }
    }
    out
}

#[cfg(test)]
mod unit_tests {
    use super::*;

    /// `encode-json-escapes` on bare metal: `u00C0  len=4 units= 15 193 128 32`.
    #[test]
    fn a_character_outside_the_alphabet_is_framed() {
        assert_eq!(units_of("aÀb"), vec![15, 193, 128, 32]);
        assert_eq!(units_of("é"), vec![97], "é is tier 0");
        assert_eq!(units_of("€"), vec![233, 168, 144], "unicode-bytes-roundtrip's 8364");
        assert_eq!(units_of("\t"), vec![68], "no tier covers a tab: `?`");
    }

    #[test]
    fn printing_follows_x86s_tables() {
        let mut out = Vec::new();
        print_bytes(&units_of("hi é"), &mut out);
        assert_eq!(out, "hi é".as_bytes());
        let mut out = Vec::new();
        print_bytes(&[193, 128], &mut out);
        assert_eq!(out, "Ā".as_bytes(), "x86's slice 0 starts at U+00C0");
        // € is tier-2 slice 7, whose delta is negative. x86 adds it unsigned in
        // a 64-bit register (`add-rr` carries REX.W), so the code point lands
        // above 2^32 and goes out as a 4-byte sequence whose low bits are
        // U+20AC: overlong.
        let mut out = Vec::new();
        print_bytes(&[233, 168, 144], &mut out);
        assert_eq!(out, vec![0xF0, 0x82, 0x82, 0xAC]);
    }

    #[test]
    fn reading_a_file_keeps_high_bytes_raw_and_drops_cr() {
        assert_eq!(read_file_units(b"A\r\n\xc3\xa9\x00B"), vec![41, 1, 195, 169]);
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
