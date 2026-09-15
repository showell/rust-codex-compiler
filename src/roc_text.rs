//! **A CODEX TEXT IN ROC IS ITS UNITS**: a `List(U8)`, one CCE unit per
//! element, as every upstream backend holds a Text (x86 a length and bytes,
//! the zig plug a `[]const u8`). Codes 1..127 are one unit per character; a
//! code outside them is FRAMED as 2, 3 or 4 units, with bands at 128, 2176 and
//! 67712. A Roc `Str` cannot carry that: it must be valid UTF-8, and a lone
//! framing unit is not.
//!
//! `text_module` writes `Text.roc`: one function per zig text part
//! (`cx_text_len`, `cx_substring`, ... in ZigEmitter.codex), behaving as the
//! interpreter does (`interp.rs`, `charcode.rs`) where the two differ. A `Str`
//! appears only at the edges: `printed` decodes units as x86's print loop does,
//! for the console, and `of_str` frames a platform's text on the way in. The
//! tables are written from `charcode.rs`'s own, not transcribed. The design is
//! the essay `notes/codex-text-in-roc.md`.

use crate::charcode;

/// A text literal as the units it holds: every character through the tiers,
/// framed, as the interpreter reads a literal (`charcode::units_of`).
pub fn literal(s: &str) -> String {
    let units: Vec<String> = charcode::units_of(s).iter().map(u8::to_string).collect();
    format!("[{}]", units.join(", "))
}

/// `Text.roc`, with its tables filled in.
pub fn text_module() -> String {
    let rows = |xs: Vec<u64>| -> String {
        xs.chunks(16)
            .map(|c| format!("\t\t{}", c.iter().map(u64::to_string).collect::<Vec<_>>().join(", ")))
            .collect::<Vec<_>>()
            .join(",\n")
    };
    let flat = |xs: &[u32]| xs.iter().map(u32::to_string).collect::<Vec<_>>().join(", ");
    let points = (0..128u8).map(|c| charcode::tier0_point(c) as u64).collect();
    let codes = (0..128u32).map(|p| charcode::code_of_point(p) as u64).collect();
    let t2_end: Vec<String> = charcode::X86_T2.iter().map(|e| (e[0] as u32 | (e[1] as u32) << 8).to_string()).collect();
    let t2_delta: Vec<String> =
        charcode::X86_T2.iter().map(|e| u32::from_le_bytes([e[2], e[3], e[4], e[5]]).to_string()).collect();
    let bases: Vec<String> = charcode::X86_T1_BASES.iter().map(u64::to_string).collect();
    TEXT.replace("@POINTS@", &rows(points))
        .replace("@CODES@", &rows(codes))
        .replace("@T1_CODE@", &flat(&charcode::T1_CODE))
        .replace("@T1_SIZE@", &flat(&charcode::T1_SIZE))
        .replace("@T1_UNI@", &flat(&charcode::T1_UNI))
        .replace("@T2_UNI@", &flat(&charcode::T2_UNI))
        .replace("@T2_SIZE@", &flat(&charcode::T2_SIZE))
        .replace("@X86_T1_BASES@", &bases.join(", "))
        .replace("@X86_T2_END@", &t2_end.join(", "))
        .replace("@X86_T2_DELTA@", &t2_delta.join(", "))
}

const TEXT: &str = r#"# Text -- a Codex Text as its CCE units, written by rocemit
# (rust-codex-compiler) from the compiler's own tables. Do not edit.
#
# A Codex Text is a sequence of units 0..255, as every upstream backend holds
# one: codes 1..127 are one unit per character, and a code outside them is
# framed as 2, 3 or 4 units. Each function is the zig plug's text part of the
# same name (`cx_*`), behaving as rust-codex-compiler's interpreter does where
# the two differ. A Str appears only at the edges: `printed` for the console,
# `of_str` for text from the platform.

Text :: [].{
	# The code point each code 0..127 names (`cce_table`); 0 for none.
	points : List(U64)
	points = [
@POINTS@
	]

	# The code of each code point below 128 (`cx_cp_to_cce`); 68, `?`, where
	# the alphabet names none.
	codes : List(U64)
	codes = [
@CODES@
	]

	# Tier 1 (`cce_t1_code`, `cce_t1_size`, `cce_t1_uni`) and tier 2
	# (`cce_t2_uni`, `cce_t2_size`, cumulative from code 2176).
	t1_code : List(U64)
	t1_code = [@T1_CODE@]

	t1_size : List(U64)
	t1_size = [@T1_SIZE@]

	t1_uni : List(U64)
	t1_uni = [@T1_UNI@]

	t2_uni : List(U64)
	t2_uni = [@T2_UNI@]

	t2_size : List(U64)
	t2_size = [@T2_SIZE@]

	# x86's print tables: the code point starting each 128-code slice of tier 1
	# (`tier1-slice-bases`), and per tier-2 slice the code it ends before and
	# the delta to its code point, added unsigned in a 64-bit register
	# (`tier2-rodata`).
	x86_t1_bases : List(U64)
	x86_t1_bases = [@X86_T1_BASES@]

	x86_t2_end : List(U64)
	x86_t2_end = [@X86_T2_END@]

	x86_t2_delta : List(U64)
	x86_t2_delta = [@X86_T2_DELTA@]

	# `text-length` (`cx_text_len`): the count of units.
	len : List(U8) -> I64
	len = |s| U64.to_i64_wrap(List.len(s))

	# `char-at` (`cx_char_at`): one unit, and no running past the end.
	char_at : List(U8), I64 -> I64
	char_at = |s, i|
		if i < 0 { crash("char-at past the end") }
		else { U64.to_i64_wrap(U8.to_u64(List.get(s, I64.to_u64_wrap(i)) ?? crash("char-at past the end"))) }

	# `char-code-at`: one unit, 0 past the end.
	char_code_at : List(U8), I64 -> I64
	char_code_at = |s, i| if i < 0 { 0 } else { U64.to_i64_wrap(U8.to_u64(List.get(s, I64.to_u64_wrap(i)) ?? 0)) }

	# `substring` (`cx_substring`), clamped to the text as the interpreter
	# clamps it.
	substring : List(U8), I64, I64 -> List(U8)
	substring = |s, start, n| List.sublist(s, { start: I64.to_u64_wrap(I64.max(start, 0)), len: I64.to_u64_wrap(I64.max(n, 0)) })

	# `text-compare` (`cx_text_compare`): unsigned unit order, -1, 0 or 1.
	compare : List(U8), List(U8) -> I64
	compare = |a, b| Text.compare_from(a, b, 0)

	compare_from : List(U8), List(U8), U64 -> I64
	compare_from = |a, b, i| {
		x = List.get(a, i)
		y = List.get(b, i)
		match (x, y) {
			(Err(_), Err(_)) => 0
			(Err(_), Ok(_)) => -1
			(Ok(_), Err(_)) => 1
			(Ok(p), Ok(q)) => if p < q { -1 } else if p > q { 1 } else { Text.compare_from(a, b, i + 1) }
		}
	}

	# `char-to-text` (`cx_char_to_text`): one unit, the code's low byte.
	char_to_text : I64 -> List(U8)
	char_to_text = |c| [I64.to_u8_wrap(c)]

	# `char-encode` (`cx_char_encode`): the code framed as 1 to 4 units.
	char_encode : I64 -> List(U8)
	char_encode = |c| Text.frame(U64.bitwise_and(I64.to_u64_wrap(c), 4294967295))

	frame : U64 -> List(U8)
	frame = |u|
		if u < 128 {
			[U64.to_u8_wrap(u)]
		} else if u < 2176 {
			v = u - 128
			[Text.low(192 + U64.div_by(v, 64)), Text.low(128 + U64.bitwise_and(v, 63))]
		} else if u < 67712 {
			v = u - 2176
			[Text.low(224 + U64.div_by(v, 4096)), Text.low(128 + U64.bitwise_and(U64.div_by(v, 64), 63)), Text.low(128 + U64.bitwise_and(v, 63))]
		} else {
			v = u - 67712
			[
				Text.low(240 + U64.div_by(v, 262144)),
				Text.low(128 + U64.bitwise_and(U64.div_by(v, 4096), 63)),
				Text.low(128 + U64.bitwise_and(U64.div_by(v, 64), 63)),
				Text.low(128 + U64.bitwise_and(v, 63)),
			]
		}

	low : U64 -> U8
	low = |v| U64.to_u8_wrap(v)

	# `text-contains`, `text-starts-with`, `text-ends-with`
	# (`cx_text_contains` ...): unit by unit, blind to frames.
	contains : List(U8), List(U8) -> Bool
	contains = |h, n| Text.find(h, n, 0) >= 0

	starts_with : List(U8), List(U8) -> Bool
	starts_with = |s, p| List.starts_with(s, p)

	ends_with : List(U8), List(U8) -> Bool
	ends_with = |s, p| List.ends_with(s, p)

	# The first index from `i` where `n` occurs in `h`, or -1.
	find : List(U8), List(U8), U64 -> I64
	find = |h, n, i|
		if i + List.len(n) > List.len(h) { -1 }
		else if List.sublist(h, { start: i, len: List.len(n) }) == n { U64.to_i64_wrap(i) }
		else { Text.find(h, n, i + 1) }

	# `text-replace` (`cx_text_replace`): every occurrence left to right, and
	# an empty pattern answers the text as it was.
	replace : List(U8), List(U8), List(U8) -> List(U8)
	replace = |s, a, b| if List.len(a) == 0 { s } else { Text.replace_from(s, a, b, 0, []) }

	replace_from : List(U8), List(U8), List(U8), U64, List(U8) -> List(U8)
	replace_from = |s, a, b, i, acc| {
		p = Text.find(s, a, i)
		if p < 0 {
			List.concat(acc, List.drop_first(s, i))
		} else {
			at = I64.to_u64_wrap(p)
			Text.replace_from(s, a, b, at + List.len(a), List.concat(List.concat(acc, List.sublist(s, { start: i, len: at - i })), b))
		}
	}

	# `text-split` (`cx_text_split`): the pieces between separators; an empty
	# separator answers the text whole.
	split : List(U8), List(U8) -> List(List(U8))
	split = |s, sep| if List.len(sep) == 0 { [s] } else { Text.split_from(s, sep, 0, []) }

	split_from : List(U8), List(U8), U64, List(List(U8)) -> List(List(U8))
	split_from = |s, sep, start, acc| {
		p = Text.find(s, sep, start)
		if p < 0 {
			List.append(acc, List.drop_first(s, start))
		} else {
			at = I64.to_u64_wrap(p)
			Text.split_from(s, sep, at + List.len(sep), List.append(acc, List.sublist(s, { start: start, len: at - start })))
		}
	}

	# `text-concat-list` (`cx_text_concat_list`).
	concat_list : List(List(U8)) -> List(U8)
	concat_list = |l| List.fold(l, [], |acc, p| List.concat(acc, p))

	# `text-to-integer` (`cx_text_to_integer`): a minus only as the first unit,
	# then decimal digits, units 3..12, until the first unit that is not one,
	# wrapping. So `+7` and ` 42` are 0, and `12abc` is 12.
	to_integer : List(U8) -> I64
	to_integer = |s| {
		neg = (List.get(s, 0) ?? 0) == 73
		n = Text.digits_from(s, if neg { 1 } else { 0 }, 0)
		if neg { I64.minus_wrap(0, n) } else { n }
	}

	digits_from : List(U8), U64, I64 -> I64
	digits_from = |s, i, acc| {
		u = Text.at(s, i)
		if u >= 3 and u <= 12 { Text.digits_from(s, i + 1, I64.plus_wrap(I64.times_wrap(acc, 10), U64.to_i64_wrap(u - 3))) } else { acc }
	}

	# `show` of an integer (`cx_show_int`): its decimal digits as units, 3 + d
	# each, and 73 for a minus.
	show_int : I64 -> List(U8)
	show_int = |n| List.map(Str.to_utf8(I64.to_str(n)), |b| if b == 45 { 73 } else { b - 45 })

	# `raw-bytes-to-text`: each integer's low byte, a unit as given.
	of_bytes : List(I64) -> List(U8)
	of_bytes = |xs| List.map(xs, |b| I64.to_u8_wrap(b))

	# A platform's Str as units (`cx_utf8_to_cce`): each code point's code,
	# framed.
	of_str : Str -> List(U8)
	of_str = |str| Text.of_utf8(Str.to_utf8(str), 0, [])

	of_utf8 : List(U8), U64, List(U8) -> List(U8)
	of_utf8 = |bytes, i, acc|
		if i >= List.len(bytes) { acc } else {
			b = Text.at(bytes, i)
			width = if b < 128 { 1 } else if b < 224 { 2 } else if b < 240 { 3 } else { 4 }
			point = if width == 1 { b } else { Text.tail(bytes, i + 1, i + width, Text.lead(b, width)) }
			Text.of_utf8(bytes, i + width, List.concat(acc, Text.frame(Text.code_of_point(point))))
		}

	lead : U64, U64 -> U64
	lead = |b, width|
		if width == 2 { U64.bitwise_and(b, 31) }
		else if width == 3 { U64.bitwise_and(b, 15) }
		else { U64.bitwise_and(b, 7) }

	tail : List(U8), U64, U64, U64 -> U64
	tail = |bytes, i, stop, acc|
		if i >= stop { acc } else { Text.tail(bytes, i + 1, stop, acc * 64 + U64.bitwise_and(Text.at(bytes, i), 63)) }

	# A unit as a U64, 0 past the end.
	at : List(U8), U64 -> U64
	at = |s, k| U8.to_u64(List.get(s, k) ?? 0)

	# `cx_cp_to_cce`: the code for a code point, tier 0 first; a point no tier
	# covers is `?`, 68.
	code_of_point : U64 -> U64
	code_of_point = |p|
		if p < 128 { List.get(Text.codes, p) ?? 68 } else { Text.high_code(p, 97) }

	high_code : U64, U64 -> U64
	high_code = |p, c|
		if c > 127 { Text.tier1_code(p, 0) }
		else if (List.get(Text.points, c) ?? 0) == p { c }
		else { Text.high_code(p, c + 1) }

	tier1_code : U64, U64 -> U64
	tier1_code = |p, k|
		if k >= List.len(Text.t1_uni) { Text.tier2_code(p, 0, 2176) } else {
			uni = List.get(Text.t1_uni, k) ?? 0
			size = List.get(Text.t1_size, k) ?? 0
			if p >= uni and p < uni + size { (List.get(Text.t1_code, k) ?? 0) + (p - uni) } else { Text.tier1_code(p, k + 1) }
		}

	tier2_code : U64, U64, U64 -> U64
	tier2_code = |p, k, base|
		if k >= List.len(Text.t2_uni) { 68 } else {
			uni = List.get(Text.t2_uni, k) ?? 0
			size = List.get(Text.t2_size, k) ?? 0
			if p >= uni and p < uni + size { base + (p - uni) } else { Text.tier2_code(p, k + 1, base + size) }
		}

	# **THE UNITS AS x86's PRINT LOOP WRITES THEM** (`emit-print-text-loop`,
	# `__cce_print_multi`), then read as UTF-8 for the platform: a unit below
	# 128 is its tier-0 code point; a unit whose top nibble is 1110 starts a
	# 3-unit tier-2 frame; every other unit from 128 is taken as a 2-unit tier-1
	# frame. Each byte is the low byte of the shifted value, and a unit past the
	# end reads as 0. A sequence x86 writes that is not UTF-8 (an overlong code
	# point from a negative tier-2 delta) arrives as U+FFFD.
	printed : List(U8) -> Str
	printed = |s| Str.from_utf8_lossy(Text.print_from(s, 0, []))

	print_from : List(U8), U64, List(U8) -> List(U8)
	print_from = |s, i, out|
		if i >= List.len(s) { out } else {
			b0 = Text.at(s, i)
			if b0 < 128 {
				Text.print_from(s, i + 1, List.concat(out, Text.utf8_3(List.get(Text.points, b0) ?? 0)))
			} else if U64.bitwise_and(b0, 240) == 224 {
				code = 2176 + U64.bitwise_and(b0, 15) * 4096 + U64.bitwise_and(Text.at(s, i + 1), 63) * 64 + U64.bitwise_and(Text.at(s, i + 2), 63)
				Text.print_from(s, i + 3, List.concat(out, Text.utf8_4(Text.x86_t2_point(code, 0))))
			} else {
				v = U64.bitwise_and(b0, 31) * 64 + U64.bitwise_and(Text.at(s, i + 1), 63)
				cp = (List.get(Text.x86_t1_bases, U64.div_by(v, 128)) ?? 0) + U64.bitwise_and(v, 127)
				Text.print_from(s, i + 2, List.concat(out, Text.utf8_3(cp)))
			}
		}

	x86_t2_point : U64, U64 -> U64
	x86_t2_point = |code, k|
		if k >= List.len(Text.x86_t2_end) { 65533 }
		else if code < (List.get(Text.x86_t2_end, k) ?? 0) { code + (List.get(Text.x86_t2_delta, k) ?? 0) }
		else { Text.x86_t2_point(code, k + 1) }

	# A code point in 1, 2 or 3 bytes.
	utf8_3 : U64 -> List(U8)
	utf8_3 = |cp|
		if cp < 128 { [Text.low(cp)] }
		else if cp < 2048 { [Text.low(U64.bitwise_or(U64.div_by(cp, 64), 192)), Text.cont(cp)] }
		else { [Text.low(U64.bitwise_or(U64.div_by(cp, 4096), 224)), Text.cont(U64.div_by(cp, 64)), Text.cont(cp)] }

	# A code point in 3 bytes below 65536 and 4 from there, as x86's tier-2
	# path writes it.
	utf8_4 : U64 -> List(U8)
	utf8_4 = |cp|
		if cp < 65536 { [Text.low(U64.bitwise_or(U64.div_by(cp, 4096), 224)), Text.cont(U64.div_by(cp, 64)), Text.cont(cp)] }
		else { [Text.low(U64.bitwise_or(U64.div_by(cp, 262144), 240)), Text.cont(U64.div_by(cp, 4096)), Text.cont(U64.div_by(cp, 64)), Text.cont(cp)] }

	# A continuation byte: the low six bits, with the top bit set.
	cont : U64 -> U8
	cont = |v| Text.low(U64.bitwise_or(U64.bitwise_and(v, 63), 128))

	# A door's answer whose text comes from the machine, as units.
	answer_units : (a, Str) -> (a, List(U8))
	answer_units = |pair| (pair.0, Text.of_str(pair.1))
}
"#;

#[cfg(test)]
mod tests {
    use super::*;

    /// `encode-json-escapes` on bare metal: `u00C0  len=4 units= 15 193 128 32`.
    #[test]
    fn a_literal_is_its_units_framed() {
        assert_eq!(literal("aÀb"), "[15, 193, 128, 32]");
        assert_eq!(literal(""), "[]");
        assert_eq!(literal("€"), "[233, 168, 144]");
    }

    #[test]
    fn the_module_is_written_from_the_tables() {
        let m = text_module();
        assert!(!m.contains('@'), "a table was left unfilled");
        // 'A' is code point 65 and code 41; code 41 names U+0041.
        let codes = m.split("codes = [").nth(1).unwrap();
        let first: Vec<&str> = codes.split(|c: char| !c.is_ascii_digit()).filter(|s| !s.is_empty()).take(128).collect();
        assert_eq!(first[65], "41");
        assert_eq!(first[9], "68", "no tier covers a tab");
        assert!(m.contains("x86_t1_bases = [192, 320,"), "x86's slice 0 starts at U+00C0");
    }
}
