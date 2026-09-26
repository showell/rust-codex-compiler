//! Roc from the IR: a unit's chapters as Roc type modules, whole, and the
//! chapter holding `opening` as an app for Roc's default Echo platform.
//!
//! The IR carries a type on every node, so this READS types rather than
//! inferring them: `int-default` is `I64`, `real` is `F64`, and every
//! definition is annotated -- Roc's unannotated fraction is a `Dec`, and the
//! safari specs grade IEEE doubles at tolerance 0.0.
//!
//! **REFUSES WHAT IT HAS NOT BUILT.** A form outside safari's subset
//! (`roc-apps/docs/codex-subset.md`) is an `Err` naming the form, never a
//! guess at Roc for it.
//!
//! Codex `Integer` is `I64` throughout; the conversions sit at the `List`
//! boundary (`List.len` is a `U64`, `List.get` takes one) and at
//! `real-to-bits`, whose Roc counterpart returns a `U64`. `list-at` out of
//! range is a runtime fault in Codex and a `crash` here.

use crate::ast::{Chapter, TypeDef, TypeExpr};
use crate::check::{RealWidth, Ty, TypeDefs};
use crate::ir_chapter::{IrActStmt, IrBinOp, IrDef, IrExpr, IrPat};
use crate::symbol::{Sym, SymTab};
use std::collections::BTreeMap;

/// Roc's reserved words, tested one at a time against the nightly. The
/// header's own vocabulary is reserved everywhere, not only in a header:
/// `targets` as a parameter name is a parse error in the middle of a
/// module (codex/test's magic-sim-fixes).
const KEYWORDS: [&str; 34] = [
    "and", "app", "as", "break", "crash", "dbg", "else", "expect", "exposes", "exposing", "for", "generates", "has",
    "hosted", "if", "implements", "import", "imports", "in", "interface", "match", "module", "or", "package",
    "packages", "platform", "provides", "requires", "return", "targets", "var", "where", "while", "with",
];

/// Roc's own type names: a chapter that declares one of these spells it
/// with a trailing underscore, since a declared `Box` reads as the
/// builtin's and Roc asks it for a type argument (codex/test's
/// literal-subpattern, tco-direct-arg-reads).
/// Modules Roc's builtins already declare: a chapter with one of these
/// names cannot be imported, since the name is taken before the program
/// starts (codex/test's forewords/encode-json-numbers declares Json).
/// Read from `src/build/roc/Builtin.roc`'s own declarations.
/// The builtins that read and write the address space. A poke answers 0
/// and is bound to a name nobody reads; the write is the point.
pub const MEMORY_OPS: [&str; 16] = [
    "peek-byte", "peek-16", "peek-32", "peek-qword", "poke-byte", "poke-16", "poke-32", "poke-qword", "alloc-bytes",
    "__heap-advance", "atomic-load", "atomic-store", "atomic-exchange", "__buf-write-byte", "__buf-write-bytes",
    "__buf-read-bytes",
];

/// The builtins the machine answers: PCI configuration space through 0xCF8
/// and 0xCFC, the MMIO pair (a load and a store, like the memory builtins,
/// answered by whatever backs the address), the block device, the keyboard's
/// two reads, and the running process's id and scope. A unit that reaches one
/// threads `Machine` where it would have threaded `Mem`, and the memory
/// builtins become the machine's doors too. The Machine module is not written
/// here: it is roc-apps' model of codex-vm and the kernel (machine/roc), and
/// whatever runs the program supplies it beside the emitted modules.
pub const MACHINE_OPS: [&str; 33] = [
    "gpu-out",
    "gpu-in",
    "gpu-mem-write",
    "gpu-mem-read",
    "process-yield",
    "net-send-raw",
    "net-recv-raw",
    "net-status",
    "net-get-hwaddr",
    "port-out-byte",
    "port-in-byte",
    "port-out-16",
    "port-in-16",
    "port-in-16-block",
    "port-out-16-block",
    "process-get-cap",
    "process-restrict-cap",
    "process-set-scope",
    "process-get-network-scope",
    "uefi-read-key-ex",
    "uefi-read-key",
    "port-out-32",
    "port-in-32",
    "read-mmio",
    "poke-mmio",
    "read-mmio-32",
    "poke-mmio-32",
    "block-read-sector",
    "block-write-sector",
    "block-sector-count",
    "block-select",
    "process-get-pid",
    "process-get-scope",
];

const ROC_MODULES: [&str; 22] = [
    "Builtin", "BLAKE3", "Box", "Crypto", "Dec", "Digest", "Encoding", "Hasher", "HttpHeader", "Iter", "Json",
    "List", "Num", "Numeral", "Range", "SHA256", "Set", "Str", "Stream", "F32", "F64", "Bool",
];

/// A chapter's Roc module name: its own, unless Roc has taken it.
fn module_ident(slug: &str) -> String {
    if ROC_MODULES.contains(&slug) {
        format!("{slug}_")
    } else {
        slug.to_string()
    }
}

const ROC_TYPES: [&str; 26] = [
    "Box", "List", "Str", "Bool", "Dict", "Set", "Result", "Try", "Num", "Int", "Frac", "Dec", "U8", "U16", "U32", "U64",
    "U128", "I8", "I16", "I32", "I64", "I128", "F32", "F64", "Iter", "Hasher",
];

fn type_name(t: &str) -> String {
    if ROC_TYPES.contains(&t) {
        format!("{t}_")
    } else {
        t.to_string()
    }
}


/// Whether a type expression holds a function (or an effect) anywhere in it.
fn holds_fun(t: &TypeExpr) -> bool {
    match t {
        TypeExpr::Fun(..) | TypeExpr::Effect(..) => true,
        TypeExpr::Named(..) => false,
        TypeExpr::App(f, args, _) => holds_fun(f) || args.iter().any(holds_fun),
        TypeExpr::BoundedInt(b, ..) | TypeExpr::Linear(b, _) | TypeExpr::Constrained(_, _, b, _) => holds_fun(b),
        TypeExpr::PropEq(a, b, _) | TypeExpr::Forall(_, a, b, _) => holds_fun(a) || holds_fun(b),
    }
}

/// Every `Named` in a type expression, however deep.
fn named_types(t: &TypeExpr, out: &mut std::collections::BTreeSet<Sym>) {
    match t {
        TypeExpr::Named(n, _) => {
            out.insert(*n);
        }
        TypeExpr::Fun(a, b, _) => {
            named_types(a, out);
            named_types(b, out);
        }
        TypeExpr::App(f, args, _) => {
            named_types(f, out);
            for a in args {
                named_types(a, out);
            }
        }
        TypeExpr::Effect(_, _, _, b, _) | TypeExpr::BoundedInt(b, ..) | TypeExpr::Linear(b, _) | TypeExpr::Constrained(_, _, b, _) => named_types(b, out),
        TypeExpr::PropEq(a, b, _) => {
            named_types(a, out);
            named_types(b, out);
        }
        TypeExpr::Forall(_, a, b, _) => {
            named_types(a, out);
            named_types(b, out);
        }
    }
}

/// The types and the arithmetic no chapter declares and Roc does not have
/// in the shape Codex means.
///
/// `int-mod` is Codex's Euclidean remainder, always in `[0, |b|)`; Roc's
/// `mod_by` is FLOORED, so it takes the divisor's sign and the two answer
/// differently for a negative divisor (7 mod -3 is 1 in Codex and -2 in
/// Roc). They agree everywhere a divisor is positive, which is everywhere
/// the corpus divides, and this says so anyway.
const MEM: &str = r#"# Mem -- Codex's address space, written by rocemit. Do not edit.
#
# `peek-byte`, `poke-32` and `alloc-bytes` read and write one heap. Codex
# gives them an empty effect row, so rocemit finds the definitions that
# touch memory by closure over the call graph and threads this value
# through them, the way it threads a GPU device.
#
# **A DOOR THAT READS OR WRITES IS AN EFFECT**, spelled `!` and typed `=>`,
# and so is every definition that reaches one: a platform may keep the bytes
# itself (roc-apps framebuffer/roc/Mem.roc). This one keeps them in the value,
# so its doors are pure underneath. The bump pointer's doors (`alloc`,
# `advance`, `mark`, `release`) are pure everywhere: the value carries it.
#
# **A PERSISTENT TRIE, NOT AN ARRAY OF PAGES.** An array is O(1) per write
# when the reference count cooperates and O(page) when it does not, and
# nothing in the source says which one you got: the difference between
# the two is one extra mention of a name. A trie is O(depth) BY
# CONSTRUCTION -- the spine is rebuilt every time, so there is no fast
# path to fall off. Five levels of 32 over 64-byte leaves is a 2 GB space
# in which a write touches five 32-wide nodes and one 64-byte leaf,
# whatever the compiler decides about sharing.
#
# It also removes the cap. There is no page table to size, so there is no
# address that reads zero and crashes when written, and an untouched
# address costs nothing at all.

Mem :: [].{
	Node := [Empty, Leaf(List(U8)), Branch(List(Mem.Node))]

	Mem : { root : Mem.Node, top : I64 }

	# 6 bits of leaf, 5 levels of 5 bits: 2^31 bytes.
	leaf_bits : U64
	leaf_bits = 6

	leaf_size : U64
	leaf_size = 64

	fan : U64
	fan = 32

	depth : I64
	depth = 5

	new : I64 -> Mem.Mem
	new = |z| { root: Empty, top: 6291456 + z }

	alloc : Mem.Mem, I64 -> (Mem.Mem, I64)
	alloc = |mem, n| ({ root: mem.root, top: mem.top + n }, mem.top)

	# `__heap-advance`: the bump pointer moves past `n` bytes.
	advance : Mem.Mem, I64 -> (Mem.Mem, {})
	advance = |mem, n| ({ root: mem.root, top: mem.top + n }, {})

	# `__heap-save` answers the bump pointer, and `__heap-restore` rewinds to it.
	mark : Mem.Mem -> (Mem.Mem, I64)
	mark = |mem| (mem, mem.top)

	release : Mem.Mem, I64 -> (Mem.Mem, I64)
	release = |mem, h| ({ root: mem.root, top: h }, 0)

	# The index into the node at `level`: level 0 is the leaf's byte.
	part : U64, I64 -> U64
	part = |a, level|
		if level <= 0 {
			U64.bitwise_and(a, 63)
		} else {
			U64.bitwise_and(U64.div_trunc_by(a, Mem.pow32(level - 1) * Mem.leaf_size), 31)
		}

	pow32 : I64 -> U64
	pow32 = |k| if k <= 0 { 1 } else { 32 * Mem.pow32(k - 1) }

	# ---- reading --------------------------------------------------------

	byte_at : Mem.Node, U64, I64 -> U8
	byte_at = |node, a, level| match node {
		Empty => 0
		Leaf(bytes) => List.get(bytes, Mem.part(a, 0)) ?? 0
		Branch(kids) => Mem.byte_at(List.get(kids, Mem.part(a, level)) ?? Empty, a, level - 1)
	}

	load! : Mem.Mem, I64, I64, I64 => (Mem.Mem, I64)
	load! = |mem, base, off, width| (mem, U64.to_i64_wrap(Mem.read(mem, base + off, width - 1, 0)))

	read : Mem.Mem, I64, I64, U64 -> U64
	read = |mem, addr, j, acc|
		if j < 0 {
			acc
		} else {
			b = Mem.byte_at(mem.root, I64.to_u64_wrap(addr + j), Mem.depth)
			Mem.read(mem, addr, j - 1, U64.plus_wrap(U64.times_wrap(acc, 256), U8.to_u64(b)))
		}

	# ---- writing --------------------------------------------------------

	store! : Mem.Mem, I64, I64, I64, I64 => (Mem.Mem, I64)
	store! = |mem, base, off, v, width| (Mem.write(mem, base + off, I64.to_u64_wrap(v), width), 0)

	# `atomic-exchange`: the qword at the address becomes `v`, and the old one
	# is the answer.
	exchange! : Mem.Mem, I64, I64 => (Mem.Mem, I64)
	exchange! = |mem, addr, v| (Mem.write(mem, addr, I64.to_u64_wrap(v), 8), U64.to_i64_wrap(Mem.read(mem, addr, 7, 0)))

	# `__buf-write-byte base off v`: the low byte of `v` at base + off;
	# answers off + 1.
	write_byte! : Mem.Mem, I64, I64, I64 => (Mem.Mem, I64)
	write_byte! = |mem, base, off, v| (Mem.write(mem, base + off, I64.to_u64_wrap(v), 1), off + 1)

	# `__buf-write-bytes base off bytes`: the low byte of each element from
	# base + off on; answers off plus the count, the offset past the last.
	write_bytes! : Mem.Mem, I64, I64, List(I64) => (Mem.Mem, I64)
	write_bytes! = |mem, base, off, bytes| (Mem.write_each(mem, base + off, bytes, 0), off + U64.to_i64_wrap(List.len(bytes)))

	write_each : Mem.Mem, I64, List(I64), U64 -> Mem.Mem
	write_each = |mem, at, bytes, i|
		match List.get(bytes, i) {
			Err(_) => mem
			Ok(b) => Mem.write_each(Mem.write(mem, at + U64.to_i64_wrap(i), I64.to_u64_wrap(b), 1), at, bytes, i + 1)
		}

	# `__buf-read-bytes base off count`: the `count` bytes from base + off on,
	# each as an unsigned value; a count of zero or less reads none.
	read_bytes! : Mem.Mem, I64, I64, I64 => (Mem.Mem, List(I64))
	read_bytes! = |mem, base, off, count| (mem, Mem.read_each(mem, base + off, count, List.with_capacity(I64.to_u64_wrap(I64.max(count, 0)))))

	read_each : Mem.Mem, I64, I64, List(I64) -> List(I64)
	read_each = |mem, at, count, acc| {
		i = U64.to_i64_wrap(List.len(acc))
		if i >= count {
			acc
		} else {
			Mem.read_each(mem, at, count, List.append(acc, U64.to_i64_wrap(Mem.read(mem, at + i, 0, 0))))
		}
	}

	write : Mem.Mem, I64, U64, I64 -> Mem.Mem
	write = |mem, addr, u, left|
		if left <= 0 {
			mem
		} else {
			put = Mem.set_at(mem.root, I64.to_u64_wrap(addr), Mem.depth, U64.to_u8_wrap(u))
			Mem.write({ root: put, top: mem.top }, addr + 1, U64.div_trunc_by(u, 256), left - 1)
		}

	# **THE CHILD COMES OUT BEFORE IT IS WRITTEN.** A list handed to a
	# closure, or still named after the set, is shared and gets copied.
	# List.replace takes the child out and leaves a placeholder, so the
	# recursion works on something it owns. tests/copycheck.sh is the
	# instrument that tells the two apart.
	set_at : Mem.Node, U64, I64, U8 -> Mem.Node
	set_at = |node, a, level, v|
		if level <= 0 {
			match node {
				Leaf(bytes) => Leaf(List.set(bytes, Mem.part(a, 0), v) ?? crash("Mem: offset outside a leaf"))
				_ => Leaf(List.set(List.repeat(0.U8, Mem.leaf_size), Mem.part(a, 0), v) ?? crash("Mem: offset outside a leaf"))
			}
		} else {
			i = Mem.part(a, level)
			kids = match node {
				Branch(cs) => cs
				_ => List.repeat(Empty, Mem.fan)
			}
			taken = List.replace(kids, i, Empty) ?? crash("Mem: index outside a node")
			Branch(List.set(taken.list, i, Mem.set_at(taken.prev, a, level - 1, v)) ?? crash("Mem: index outside a node"))
		}
}
"#;

const PRELUDE: &str = r#"# Prelude -- what no chapter declares, written by rocemit. Do not edit.

Prelude :: [].{
	Maybe(a) : [None, Just(a)]

	# **`~=` IS FOUR ULPs APART, NOT A TOLERANCE.** Codex compares the
	# ORDINAL of the two doubles -- the bit pattern read as a signed
	# integer, with the negatives reflected so the order is monotone --
	# and answers True when they are within four steps of each other.
	# That is a distance in representable numbers, so it is as tight near
	# zero as it is near 1e300, which no epsilon is (interp.rs `ordinal`).
	# **A REAL PRINTS AS CODEX'S OWN PRINTER PRINTS IT**, which is not
	# Rust's Display and not the shortest round-trip: the integer part in
	# full from a truncation to i64, then a point, then the fraction
	# truncated to fifteen digits with trailing zeros dropped and at
	# least one kept. `4000.0`, `0.416666666666666`, `1.5`. The verdicts
	# in codex/test are what this is checked against; our Rust
	# interpreter prints Rust's way and disagrees with them, which is a
	# bug on that side and the reason this is written from the verdicts.
	real_to_str : F64 -> Str
	real_to_str = |f|
		if F64.is_nan(f) { "nan" }
		else if F64.is_infinite(f) { if f < 0.0 { "-inf" } else { "inf" } }
		else if F64.abs(f) >= 9223372036854775808.0 {
			if f < 0.0 { Str.concat("-", Prelude.wide_to_str(F64.abs(f))) } else { Prelude.wide_to_str(f) }
		}
		else {
			neg = f < 0.0
			a = F64.abs(f)
			ip = F64.to_i64_wrap(a)
			frac = a - I64.to_f64(ip)
			digits = Prelude.frac_digits(frac, 15, [])
			body = Str.concat(Str.concat(I64.to_str(ip), "."), Prelude.digits_str(Prelude.trim_zeros(digits)))
			if neg { Str.concat("-", body) } else { body }
		}

	# From 2^63 up Codex prints exponent form (U62, COMPILER-41): 15
	# significant digits rounded half to even, trailing zeros dropped but one
	# kept, then `e+NN`. Upstream rounds the EXACT integer (long division over
	# 32-bit limbs); this scales by a power of ten, which agrees except where
	# the digits past the fifteenth are an exact tie.
	wide_to_str : F64 -> Str
	wide_to_str = |a| {
		e = Prelude.decimal_exponent(a, 0)
		scaled = a / F64.pow(10.0, I64.to_f64(e - 14))
		# Positive and under 10^16, so truncation is the floor.
		base = F64.to_i64_wrap(scaled)
		r = scaled - I64.to_f64(base)
		up = r > 0.5 or (r == 0.5 and I64.rem_by(base, 2) == 1)
		m0 = if up { base + 1 } else { base }
		# Rounding up can carry into a sixteenth digit.
		(m, ex) = if m0 >= 1000000000000000 { (I64.div_trunc_by(m0, 10), e + 1) } else { (m0, e) }
		s = I64.to_str(m)
		lead = Str.from_utf8_lossy(List.take_first(Str.to_utf8(s), 1))
		rest = Str.from_utf8_lossy(List.drop_first(Str.to_utf8(s), 1))
		trimmed = Prelude.trim_zero_text(rest)
		Str.concat(Str.concat(Str.concat(lead, "."), if Str.is_empty(trimmed) { "0" } else { trimmed }), Str.concat("e+", I64.to_str(ex)))
	}

	decimal_exponent : F64, I64 -> I64
	decimal_exponent = |a, e| if a >= 10.0 { Prelude.decimal_exponent(a / 10.0, e + 1) } else { e }

	trim_zero_text : Str -> Str
	trim_zero_text = |t| {
		bs = Str.to_utf8(t)
		Str.from_utf8_lossy(Prelude.drop_trailing_zeros(bs))
	}

	drop_trailing_zeros : List(U8) -> List(U8)
	drop_trailing_zeros = |bs| if List.last(bs) == Ok(48) { Prelude.drop_trailing_zeros(List.drop_last(bs, 1)) } else { bs }

	# The fraction's digits, most significant first, by taking one at a
	# time; `n` bounds it at the width Codex's printer carries.
	frac_digits : F64, I64, List(I64) -> List(I64)
	frac_digits = |frac, n, acc|
		if n <= 0 { acc } else {
			scaled = frac * 10.0
			d = F64.to_i64_wrap(scaled)
			Prelude.frac_digits(scaled - I64.to_f64(d), n - 1, List.append(acc, d))
		}

	# Trailing zeros go, but a real always shows a fraction digit.
	trim_zeros : List(I64) -> List(I64)
	trim_zeros = |ds|
		match List.last(ds) {
			Ok(0) => if List.len(ds) <= 1 { ds } else { Prelude.trim_zeros(List.drop_last(ds, 1)) }
			_ => ds
		}

	digits_str : List(I64) -> Str
	digits_str = |ds| List.fold(ds, "", |acc, d| Str.concat(acc, I64.to_str(d)))

	ordinal : F64 -> I64
	ordinal = |f| {
		b = U64.to_i64_wrap(F64.to_bits(f))
		if b < 0 { I64.plus_wrap(I64.bitwise_xor(b, 9223372036854775807), 1) } else { b }
	}

	approx_eq : F64, F64 -> Bool
	approx_eq = |x, y| I64.abs(I64.minus_wrap(Prelude.ordinal(x), Prelude.ordinal(y))) <= 4

	# `ordinal` and `approx_eq` over an f32's bits: `~` on a `Real
	# approximate` counts f32 units.
	ordinal32 : F32 -> I64
	ordinal32 = |f| {
		b = I32.to_i64(U32.to_i32_wrap(F32.to_bits(f)))
		if b < 0 { I64.plus_wrap(I64.bitwise_xor(b, 2147483647), 1) } else { b }
	}

	approx_eq32 : F32, F32 -> Bool
	approx_eq32 = |x, y| I64.abs(I64.minus_wrap(Prelude.ordinal32(x), Prelude.ordinal32(y))) <= 4

	# A `saturating` Real answers the largest finite value for an infinity and
	# 0 for NaN; a `trapping` one traps on either (codex/test's
	# ops/real-saturating, real-approx-modes).
	sat_f64 : F64 -> F64
	sat_f64 = |x| if F64.is_nan(x) { 0.0 } else if F64.is_infinite(x) { if x > 0.0 { F64.from_bits(9218868437227405311) } else { F64.from_bits(18442240474082181119) } } else { x }

	sat_f32 : F32 -> F32
	sat_f32 = |x| if F32.is_nan(x) { F32.from_bits(0) } else if F32.is_infinite(x) { if x > F32.from_bits(0) { F32.from_bits(2139095039) } else { F32.from_bits(4286578687) } } else { x }

	trap_f64 : F64 -> F64
	trap_f64 = |x| if F64.is_finite(x) { x } else { crash("a trapping Real left the finite range") }

	trap_f32 : F32 -> F32
	trap_f32 = |x| if F32.is_finite(x) { x } else { crash("a trapping Real left the finite range") }

	# `a ^ b` with a negative exponent is 0, where Roc's pow crashes
	# (codex/test's ops/int-pow: `ipow 5 (0 - 2)` is 0).
	int_pow : I64, I64 -> I64
	int_pow = |a, b| if b < 0 { 0 } else { I64.pow(a, b) }

	# `base` with `pushed` appended last to first: the list a definition builds
	# by pushing onto its own recursive call, which rocemit writes as a loop
	# that gathers the pushed elements outermost first.
	push_backwards : List(a), List(a) -> List(a)
	push_backwards = |base, pushed| {
		var $out = base
		var $i = List.len(pushed)
		while $i > 0 {
			$i = $i - 1
			$out = List.append($out, List.get(pushed, $i) ?? crash("Prelude: an index outside a list"))
		}
		$out
	}

	# x86's abs negates with a wrapping neg: the most negative integer answers itself.
	int_abs : I64 -> I64
	int_abs = |a| if a < 0 { I64.minus_wrap(0, a) } else { a }

	int_mod : I64, I64 -> I64
	int_mod = |a, b| {
		m = I64.mod_by(a, b)
		if m < 0 { m + I64.abs(b) } else { m }
	}
}
"#;

/// The same helper, as an item of a chapter module.
const LINE_HELPER_INDENTED: &str =
    "\t# The Echo platform's echo! writes no newline; a Codex line is one.\n\tline! = |s| echo!(Str.concat(s, \"\\n\"))\n";

const LINE_HELPER: &str =
    "\n# The Echo platform's echo! writes no newline; a Codex line is one.\nline! = |s| echo!(Str.concat(s, \"\\n\"))\n";

/// The unit as Roc TYPE MODULES, one per Codex chapter, and one app for the
/// chapter that holds `opening`: `(<file name>, <text>)` pairs.
///
/// A chapter becomes a void module, `Slug :: [].{ ... }`, whose associated
/// items are the chapter's type definitions and definitions; another module
/// reaches them as `Slug.name`. Roc's module documentation recommends
/// exactly this shape for a namespace of functions, and it is what lets the
/// screensaver itself import the same chapters the specs grade. The app is
/// the spec's own definitions and `main!`.
/// `vm_flags` says the unit brings codex-vm flags (a `.vmargs` beside it): it
/// asks for devices only the machine answers, so it threads `Machine` even
/// where its code reaches memory alone. `by_reach` picks the state from what
/// the opening reaches, for a platform whose host stops at an address it does
/// not back (see the closure in `Cx::new`).
pub fn emit_modules(
    ch: &Chapter,
    tds: &TypeDefs,
    syms: &SymTab,
    defs: &[IrDef],
    vm_flags: bool,
    by_reach: bool,
    whole: bool,
    seed: &[(Sym, String)],
) -> Result<(Vec<(String, String)>, Vec<String>), String> {
    let called_back = crate::roc_forwarders::call_back_directly(defs);
    let defs = &called_back[..];
    if !whole {
        return emit_round(ch, tds, syms, defs, vm_flags, by_reach, None).map(|(files, _)| (files, Vec::new()));
    }
    // A round writes what it can and names what it could not; their
    // dependents are then decided too (`settle_fates`), and the next round
    // writes with every fate known. It ends when a round finds nothing new.
    // `seed`: what an earlier pass could not rewrite (`list_versions`).
    let mut fates: BTreeMap<Sym, Fate> = BTreeMap::new();
    for (n, why) in seed {
        let d = defs.iter().find(|d| d.name == *n);
        let fate = if d.is_some_and(|d| d.params.is_empty()) { Fate::Omit(why.clone()) } else { Fate::Stub(why.clone()) };
        fates.insert(*n, fate);
    }
    if !fates.is_empty() {
        settle_fates(defs, syms, &mut fates);
    }
    loop {
        let (files, failed) = emit_round(ch, tds, syms, defs, vm_flags, by_reach, Some(&fates))?;
        if failed.is_empty() {
            // What was not written as written, for whoever runs this.
            let notes = fates
                .iter()
                .map(|(n, f)| match f {
                    Fate::Stub(why) => format!("stubbed `{}`: {why}", syms.text(*n)),
                    Fate::Omit(why) => format!("left out `{}`: {why}", syms.text(*n)),
                })
                .collect();
            return Ok((files, notes));
        }
        for (n, why) in failed {
            let d = defs.iter().find(|d| d.name == n);
            let fate = if d.is_some_and(|d| d.params.is_empty()) { Fate::Omit(why) } else { Fate::Stub(why) };
            fates.insert(n, fate);
        }
        settle_fates(defs, syms, &mut fates);
    }
}

/// What whole mode does with a definition it will not write as written.
#[derive(Clone, Debug)]
pub enum Fate {
    /// A function: its body is `crash` with the reason.
    Stub(String),
    /// A constant, or a lifted lambda whose users are all gone: not
    /// written at all, and why.
    Omit(String),
}

/// The dependents of what is stubbed or left out, to a fixed point. A
/// definition that names one left out cannot compile: a function is stubbed,
/// a constant left out. A constant whose evaluation could reach a stub is
/// left out as well, since Roc evaluates it while compiling; any call it can
/// reach counts, taken or not.
fn settle_fates(defs: &[IrDef], syms: &SymTab, fates: &mut BTreeMap<Sym, Fate>) {
    let refs: BTreeMap<Sym, Vec<Sym>> = defs
        .iter()
        .map(|d| {
            let mut out = Vec::new();
            d.body.walk(&mut |x| {
                if let IrExpr::Name(m, _, _) = x {
                    out.push(*m);
                }
            });
            (d.name, out)
        })
        .collect();
    loop {
        let mut changed = false;
        for d in defs {
            if fates.contains_key(&d.name) || syms.text(d.name) == "opening" {
                continue;
            }
            let omitted = refs[&d.name].iter().find(|m| matches!(fates.get(m), Some(Fate::Omit(_))));
            let fate = if let Some(m) = omitted {
                let why = format!("it uses `{}`, which rocemit could not write", syms.text(*m));
                Some(if d.params.is_empty() { Fate::Omit(why) } else { Fate::Stub(why) })
            } else if d.params.is_empty() {
                // Everything this constant's evaluation can reach.
                let mut seen: std::collections::BTreeSet<Sym> = Default::default();
                let mut stack = refs[&d.name].clone();
                let mut hits_stub = None;
                while let Some(m) = stack.pop() {
                    if !seen.insert(m) {
                        continue;
                    }
                    if matches!(fates.get(&m), Some(Fate::Stub(_))) {
                        hits_stub = Some(m);
                        break;
                    }
                    if let Some(r) = refs.get(&m) {
                        stack.extend(r.iter().copied());
                    }
                }
                hits_stub.map(|m| {
                    Fate::Omit(format!("Roc evaluates it while compiling, and it can reach `{}`, a stub", syms.text(m)))
                })
            } else {
                None
            };
            if let Some(f) = fate {
                fates.insert(d.name, f);
                changed = true;
            }
        }
        // A LIFTED LAMBDA BELONGS TO THE DEFINITION IT WAS LIFTED OUT OF.
        // When every user of one is stubbed or left out it goes too: it is
        // not part of the chapter, and it is typed at the use that is gone
        // (a dictionary's `\x y -> y`, lowered at its instance, is `I64, a
        // -> I64`, which Roc rightly rejects).
        for d in defs {
            if fates.contains_key(&d.name) || !syms.text(d.name).starts_with("__lam_") {
                continue;
            }
            let users: Vec<Sym> =
                defs.iter().filter(|u| u.name != d.name && refs[&u.name].contains(&d.name)).map(|u| u.name).collect();
            if users.iter().all(|u| fates.contains_key(u)) {
                let why = match users.first() {
                    Some(u) => format!("it was lifted out of `{}`, which rocemit could not write", syms.text(*u)),
                    None => "nothing uses it".to_string(),
                };
                fates.insert(d.name, Fate::Omit(why));
                changed = true;
            }
        }
        if !changed {
            return;
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn emit_round(
    ch: &Chapter,
    tds: &TypeDefs,
    syms: &SymTab,
    defs: &[IrDef],
    vm_flags: bool,
    by_reach: bool,
    fates: Option<&BTreeMap<Sym, Fate>>,
) -> Result<(Vec<(String, String)>, Vec<(Sym, String)>), String> {
    let mut cx = Cx::new(ch, tds, syms, defs, vm_flags, by_reach);
    if let Some(f) = fates {
        cx.whole = true;
        cx.fates = f.clone();
    }
    // **A UNIT WITH NO OPENING IS A LIBRARY**: every chapter a module, no
    // app. That is what a GPU kernel chapter is.
    // A `[Device]` opening (GlobeKernels has one, for the wgsl plug's root)
    // is a kernel like any other, not a main.
    let device_defs = cx.device_defs.clone();
    let is_main = |d: &IrDef| syms.text(d.name) == "opening" && !device_defs.contains(&d.name);
    let app_slug = defs.iter().find(|d| is_main(d)).map(|a| module_slug(&a.origin)).unwrap_or_default();
    cx.app = app_slug.clone();
    let mut slugs: Vec<String> = Vec::new();
    let mut chapter_of: BTreeMap<String, String> = BTreeMap::new();
    for d in defs {
        if d.origin.is_empty() {
            return Err(format!("`{}` belongs to no chapter", syms.text(d.name)));
        }
        claim_module(&mut slugs, &mut chapter_of, &d.origin)?;
    }
    for c in &ch.type_def_chapters {
        claim_module(&mut slugs, &mut chapter_of, c)?;
    }
    let mut files = Vec::new();
    let undeclared: Vec<String> = ch
        .type_defs
        .iter()
        .filter(|td| has_free_field_binder(td, syms))
        .filter_map(|td| match td {
            crate::ast::TypeDef::Record(n, ..) => Some(type_name(syms.text(*n))),
            _ => None,
        })
        .collect();
    cx.undeclared = undeclared.clone();
    // Who each emitted module imports, for the prune below.
    let mut needs: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut prelude = false;
    let mut memory = false;
    for slug in &slugs {
        module_name(slug)?;
        // **THE STATE'S MODULES SIT BESIDE THE CHAPTERS'.** `Mem` is written
        // here and the machine's modules (`Machine`, `MachinePci`, ...) are
        // copied in by whatever runs the program, so a chapter spelled like
        // one would be overwritten by it or overwrite it.
        let taken = match cx.state {
            "Mem" => slug == "Mem",
            "Machine" => slug.starts_with("Machine"),
            _ => false,
        };
        if taken {
            return Err(format!("chapter module `{slug}` is a name the threaded {} holds", cx.state));
        }
        if slug == "CceText" || slug == "CceChar" {
            return Err(format!("chapter module `{slug}` is the name one of rocemit's text modules holds"));
        }
        cx.current = slug.clone();
        cx.imports.clear();
        // The helper is per MODULE now: a chapter with a [Console] act
        // prints as much as an opening does.
        cx.uses_line = false;
        let mut items = String::new();
        let base = if *slug == app_slug { 0 } else { 1 };
        for (td, c) in ch.type_defs.iter().zip(&ch.type_def_chapters) {
            // **A FIELD GENERIC IN A VARIABLE OF ITS OWN HAS NO ROC TYPE.** A
            // class dictionary for `m : a, b -> b` is `CDict (a)` with a field
            // over `b`, which Roc cannot declare ("type variable b is not
            // declared"), and it checks every declaration whether or not
            // anything uses it. It is upstream's typed-backend boundary too
            // (MethodLocalPolymorphism.md, stage 3: UNSUPPORTED_FREE_BINDER).
            // So it is not declared. A dictionary used through a call is a
            // direct call by now; one that is still used as a value fails in
            // Roc as an undeclared type, which is that boundary, named.
            if module_slug(c) == *slug {
                if !has_free_field_binder(td, syms) {
                    items.push_str(&cx.type_def(td, base)?);
                }
            }
        }
        let mut main = None;
        for d in defs.iter().filter(|d| module_slug(&d.origin) == *slug) {
            if is_main(d) {
                main = Some(cx.opening(d)?);
                continue;
            }
            // **NO `==` ON A TYPE THAT HOLDS A FUNCTION.** Codex derives one
            // for every declared sum; Roc cannot compare functions, and it
            // checks a definition even when nothing calls it. A call that
            // does reach one is refused (`unwritable_eq`).
            if cx.unwritable_eq(d.name).is_some() {
                continue;
            }
            if cx.whole {
                if let Some(t) = cx.def_or_stub(d, base) {
                    items.push('\n');
                    items.push_str(&t);
                }
                continue;
            }
            items.push('\n');
            items.push_str(&cx.def(d, base)?);
        }
        if items.is_empty() && main.is_none() {
            continue;
        }
        prelude |= cx.imports.contains("Prelude");
        memory |= cx.imports.contains("Mem");
        // A literal, an `&` or a type is enough to need `CceText.roc`, and `CceText.roc`
        // needs `CceChar.roc`.
        cx.uses_text |= cx.imports.contains("CceText");
        cx.uses_char |= cx.imports.contains("CceChar");
        let mut text = format!("# {} -- emitted from Codex by rocemit (rust-codex-compiler). Do not edit.\n", module_ident(slug));
        for m in &cx.imports {
            text.push_str(&format!("import {m}\n"));
        }
        if let Some(main) = main {
            if cx.uses_line {
                text.push_str(LINE_HELPER);
            }
            text.push_str(&items);
            text.push_str("\n# --- Entry ---\n\n");
            text.push_str(&main);
        } else {
            let helper = if cx.uses_line { LINE_HELPER_INDENTED } else { "" };
            text.push_str(&format!("\n{} :: [].{{\n{helper}{items}}}\n", module_ident(slug)));
        }
        needs.insert(module_ident(slug), cx.imports.iter().cloned().collect());
        files.push((format!("{}.roc", module_ident(slug)), text));
    }
    if cx.uses_text {
        needs.insert("CceText".into(), vec!["CceChar".into()]);
        files.push(("CceText.roc".into(), crate::roc_text::text_module()));
    }
    if cx.uses_text || cx.uses_char {
        needs.insert("CceChar".into(), Vec::new());
        files.push(("CceChar.roc".into(), crate::roc_text::char_module()));
    }
    if prelude {
        needs.insert("Prelude".into(), Vec::new());
        files.push(("Prelude.roc".into(), PRELUDE.into()));
    }
    if memory {
        needs.insert("Mem".into(), Vec::new());
        files.push(("Mem.roc".into(), MEM.into()));
    }
    // **A CHAPTER NOTHING REACHES IS NOT PART OF THE PROGRAM.** Every unit
    // is bundled with ListUtils and Tuple whether it cites them or not
    // (bundle.rs calls them implicit), and a unit that cites a chapter for
    // one of its types drags that chapter's whole cite closure in. Emitting
    // a module the app never reaches costs the reader a file and the
    // compiler a check; the import graph is right here, so the prune is
    // here rather than in whatever reads the directory afterwards.
    //
    // A LIBRARY keeps everything: with no app there is no root to reach
    // from, and its modules are the output.
    if !app_slug.is_empty() {
        let mut seen: std::collections::BTreeSet<String> = Default::default();
        let mut stack = vec![module_ident(&app_slug)];
        while let Some(m) = stack.pop() {
            if !seen.insert(m.clone()) {
                continue;
            }
            stack.extend(needs.get(&m).cloned().unwrap_or_default());
        }
        files.retain(|(name, _)| seen.contains(name.trim_end_matches(".roc")));
    }
    // **A DICTIONARY LEFT UNDECLARED BUT STILL USED IS REFUSED, BY NAME.**
    // Stage 2 turns every projection of a generated dictionary into a direct
    // call; one that is passed on, stored, or reached through a shadowed name
    // is a runtime value whose field is generic in a variable of its own, and
    // no Roc type holds it. Upstream's typed backends refuse the same thing
    // (UNSUPPORTED_FREE_BINDER); saying so beats an undeclared-type error.
    for (_, text) in &files {
        if let Some(n) = undeclared.iter().find(|n| mentions(text, n)) {
            return Err(format!("class dictionary `{n}` is used as a value, and its methods are generic in type variables of their own: no Roc type holds it (upstream's typed backends refuse it too: UNSUPPORTED_FREE_BINDER)"));
        }
    }
    Ok((files, std::mem::take(&mut cx.failed)))
}

/// The module a chapter becomes: its name without the quire, its words run
/// together, each capitalised. A cited chapter's header is `Quire--Name` and a
/// program's is written as prose (`With-Timeout Test`), while a Roc module
/// name is one capitalised alphanumeric word. Two chapters that come out the
/// same are refused where the modules are collected (`claim_module`).
fn module_slug(chapter: &str) -> String {
    let name = chapter.rsplit_once("--").map_or(chapter, |(_, name)| name);
    name.split(|c: char| !c.is_ascii_alphanumeric())
        .filter(|w| !w.is_empty())
        .map(|w| w[..1].to_ascii_uppercase() + &w[1..])
        .collect()
}

/// Add `chapter`'s module to `slugs`, refusing a second chapter that comes out
/// as the same module: their definitions would share one file.
fn claim_module(slugs: &mut Vec<String>, chapter_of: &mut BTreeMap<String, String>, chapter: &str) -> Result<(), String> {
    let s = module_slug(chapter);
    match chapter_of.get(&s) {
        Some(c) if c != chapter => Err(format!("chapters `{c}` and `{chapter}` are both module `{s}`")),
        Some(_) => Ok(()),
        None => {
            chapter_of.insert(s.clone(), chapter.to_string());
            slugs.push(s);
            Ok(())
        }
    }
}

/// A chapter slug as a Roc module name: capitalised, alphanumeric, and not
/// one Roc has already taken.
fn module_name(slug: &str) -> Result<String, String> {
    if slug.starts_with(|c: char| c.is_ascii_uppercase()) && slug.chars().all(|c| c.is_ascii_alphanumeric()) {
        Ok(module_ident(slug))
    } else {
        Err(format!("chapter `{slug}` is not a Roc module name"))
    }
}

struct Cx<'a> {
    syms: &'a SymTab,
    tds: &'a TypeDefs,
    defs: &'a [IrDef],
    /// Every emitted definition and its parameter count: a call must be
    /// saturated, because Roc calls are.
    arity: BTreeMap<Sym, usize>,
    /// Which chapter each definition and each declared type lives in.
    def_module: BTreeMap<Sym, String>,
    type_module: BTreeMap<Sym, String>,
    maybe: Sym,
    /// The chapter being emitted, and the modules its text has reached for.
    current: String,
    /// The chapter holding the opening, emitted as the app rather than a
    /// type module; empty for a library.
    app: String,
    /// **A TYPE THAT STANDS ON A CYCLE IS NOMINAL.** Roc's `:` is a
    /// transparent synonym and may not be recursive, directly or mutually;
    /// `:=` is a nominal type and may. Its constructors are still written
    /// bare, here and in every other module, so only the definition's
    /// spelling changes (verified on the nightly).
    recursive: std::collections::BTreeSet<Sym>,
    /// The types written `:=`: the recursive ones, and **EVERY RECORD TYPE** without
    /// type parameters. A
    /// `:` record is structural, so two Codex records of one shape (`Byte` and
    /// `Wide`, both `{ val }`) would be one Roc type, and which one a value was
    /// would be lost; a nominal keeps the name, and is built `Name.{ .. }`.
    nominal: std::collections::BTreeSet<Sym>,
    /// The chapter's derived `__eq_<T>`, by the type it compares. A nominal
    /// type has no structural `==`, so the one Codex derived is attached to
    /// it as the `is_eq` method Roc's `==` dispatches to.
    derived_eq: BTreeMap<Sym, Sym>,
    /// Declared types that hold a function, in a field or through a declared
    /// type they mention. Roc has no `==` for them (`unwritable_eq`).
    fun_holding: std::collections::BTreeSet<Sym>,
    imports: std::collections::BTreeSet<String>,
    /// Names bound by the enclosing parameters, lets and patterns.
    locals: Vec<Sym>,
    /// Type-variable letters, per definition signature.
    tvars: BTreeMap<u32, String>,
    uses_line: bool,
    /// Set when the unit reaches for a text helper, which is then emitted
    /// beside the chapters as `CceText.roc` (`roc_text`).
    uses_text: bool,
    /// A Codex `Char` appeared: `CceChar.roc` is written (and `CceText.roc` always needs it).
    uses_char: bool,
    /// The match being written is on a Char, as its code; see `scrutinee`.
    char_match: bool,
    /// Set while a right fold's body is emitted: its leaves become
    /// accumulator steps (see `def`).
    fold: Option<Fold>,
    /// **THE DEVICE EFFECT IS STATE.** A `[Device]` definition takes the
    /// device as its first parameter and answers `(Device.Device, T)`; the
    /// effect's operations are `Device.load`, `Device.store` and the index
    /// reads on the hand-written `Device` module (roc-apps/gpu/roc). These
    /// are the operations the chapter declares under `effect Device` and
    /// the definitions whose type carries the effect.
    device_ops: std::collections::BTreeSet<Sym>,
    device_defs: std::collections::BTreeSet<Sym>,
    /// The definitions whose signature takes `=>`. Roc spells an effectful
    /// function's name with a trailing `!`, so `def` and `def_ref` read the
    /// name off this set (`takes_bang`).
    bang_defs: std::collections::BTreeSet<Sym>,
    /// Definitions the opening cannot reach that reach a device builtin, in a
    /// unit that runs without the machine, each with the builtin it reaches.
    stubbed: BTreeMap<Sym, Sym>,
    /// **WHOLE MODE** (`rocemit --whole`): every definition of every chapter is
    /// written, and one rocemit cannot write is a `crash` stub if it is a
    /// function and left out if it is a constant. Roc evaluates a top-level
    /// constant while it compiles, so a stubbed constant is a compile error
    /// even when nothing uses it; a stubbed function compiles cleanly and
    /// crashes, with its reason, only if a program calls it (verified on the
    /// nightly). `fates` is what an earlier round decided; `failed` is what
    /// this round could not write.
    whole: bool,
    /// Class dictionaries with no Roc type (`has_free_field_binder`): whole
    /// mode stubs a definition whose text names one.
    undeclared: Vec<String>,
    fates: BTreeMap<Sym, Fate>,
    failed: Vec<(Sym, String)>,
    /// **THE STATE THIS UNIT THREADS.** `Device` for a GPU kernel, whose
    /// type says so; `Mem` for a program that reads and writes an address
    /// space, whose type does NOT: Codex gives `peek-byte` and friends an
    /// empty effect row, so the definitions that touch memory are found by
    /// closure over the call graph instead (`new`); and `Machine` when that
    /// closure reaches a port or the block device as well (`MACHINE_OPS`).
    state: &'static str,
    /// The name holding the state at this point of an effectful body, and
    /// the count of names minted for it in this definition.
    dev: Option<String>,
    dev_n: usize,
    /// Set while emitting a definition or opening that threads memory: there
    /// a heap mark is the bump pointer (`__heap-save` answers it and
    /// `__heap-restore` rewinds to it), and elsewhere, with no heap, it is 0.
    heap_live: bool,
    /// **A POKE CAN STAND ANYWHERE.** The memory builtins carry an empty
    /// effect row, so Codex writes `show (raw-mem 786432 42)` where a
    /// `[Device]` act would have had to bind the call with `<-`. Such a
    /// call is lifted out to a binding ahead of the expression that reads
    /// it; these are the bindings owed to the enclosing block, in the
    /// order they must be written.
    hoist: Vec<String>,
    tmp_n: usize,
    /// **A UNIT WITH A DEVICE KERNEL COMPUTES AS THE PLUG'S WGSL DOES.** The
    /// wgsl plug lowers Integer to `i32` and Real to `f32`, and WGSL's
    /// integer arithmetic wraps, its division by zero yields the dividend
    /// and its remainder by zero yields zero. A kernel's pixels are those
    /// bits (EarthKernel packs an alpha of `255 * 16777216`, past i32), so
    /// such a unit is spelled in I32 and F32, with the wrapping operations
    /// and `Device.div`/`Device.rem`, where a plain `+` on Roc's I32 crashes
    /// on overflow. Every other unit is I64 and F64, as safari is.
    wgsl: bool,
}

/// **NOTHING READS THE LAST ADDRESS SPACE.** main! threads `mem`, `mem1`,
/// ... and the final one is the memory at the end of the program, which no
/// statement follows; Roc warns on a binding nobody reads and a warning is
/// exit 2, so that one is spelled with the underscore Roc asks for.
fn seal_state(out: String, memory: bool, base: &str, n: usize) -> String {
    if !memory {
        return out;
    }
    let last = if n == 0 { base.to_string() } else { format!("{base}{n}") };
    let bind = format!("({last}, ");
    if out.matches(&bind).count() != 1 {
        return out;
    }
    let rest: Vec<&str> = out.split(&bind).collect();
    // The name is read elsewhere only if it appears outside its binding.
    if rest.iter().any(|part| mentions(part, &last)) {
        return out;
    }
    out.replace(&bind, &format!("(_{last}, "))
}

fn mentions(text: &str, name: &str) -> bool {
    let ok = |c: char| c.is_ascii_alphanumeric() || c == '_';
    let mut at = 0;
    while let Some(i) = text[at..].find(name) {
        let i = at + i;
        let before = text[..i].chars().next_back().is_some_and(ok);
        let after = text[i + name.len()..].chars().next().is_some_and(ok);
        if !before && !after {
            return true;
        }
        at = i + name.len();
    }
    false
}

#[derive(Clone)]
struct Fold {
    name: Sym,
    helper: String,
    acc: String,
    /// Built by pushing onto the recursive call (`is_push_fold`), not by
    /// appending it (`is_right_fold`).
    push: bool,
}

impl<'a> Cx<'a> {
    fn new(ch: &Chapter, tds: &'a TypeDefs, syms: &'a SymTab, defs: &'a [IrDef], vm_flags: bool, by_reach: bool) -> Cx<'a> {
        let mut cx = Cx {
            syms,
            tds,
            defs,
            arity: defs.iter().map(|d| (d.name, d.params.len())).collect(),
            def_module: BTreeMap::new(),
            type_module: BTreeMap::new(),
            maybe: syms.find("Maybe").unwrap_or_default(),
            current: String::new(),
            app: String::new(),
            recursive: Default::default(),
            nominal: Default::default(),
            derived_eq: BTreeMap::new(),
            fun_holding: Default::default(),
            imports: Default::default(),
            locals: Vec::new(),
            tvars: BTreeMap::new(),
            uses_line: false,
            uses_text: false,
            uses_char: false,
            char_match: false,
            fold: None,
            device_ops: Default::default(),
            device_defs: Default::default(),
            bang_defs: Default::default(),
            stubbed: Default::default(),
            whole: false,
            undeclared: Vec::new(),
            fates: Default::default(),
            failed: Vec::new(),
            state: "Device",
            dev: None,
            dev_n: 0,
            heap_live: false,
            hoist: Vec::new(),
            tmp_n: 0,
            wgsl: false,
        };
        for ed in &ch.effect_defs {
            if ch.syms.text(ed.name) != "Device" {
                continue;
            }
            for op in &ed.ops {
                if let Some(s) = syms.find(ch.syms.text(op.name)) {
                    cx.device_ops.insert(s);
                }
            }
        }
        for d in defs {
            if cx.has_device(&d.ty) {
                cx.device_defs.insert(d.name);
            }
        }
        cx.wgsl = !cx.device_defs.is_empty();
        // No kernel, so look for memory and devices. A definition touches
        // them if it calls one of the builtins or calls something that does,
        // and the closure runs until nothing new joins. A device builtin
        // reached anywhere makes the state the machine.
        if cx.device_defs.is_empty() {
            let devices: std::collections::BTreeSet<Sym> = MACHINE_OPS.iter().filter_map(|b| syms.find(b)).collect();
            let ops: std::collections::BTreeSet<Sym> =
                MEMORY_OPS.iter().filter_map(|b| syms.find(b)).chain(devices.iter().copied()).collect();
            if !ops.is_empty() {
                let mut touch: std::collections::BTreeSet<Sym> = Default::default();
                loop {
                    let mut grew = false;
                    for d in defs {
                        if touch.contains(&d.name) {
                            continue;
                        }
                        let mut hit = false;
                        d.body.walk(&mut |x| {
                            if let IrExpr::Name(n, _, _) = x {
                                if ops.contains(n) || touch.contains(n) {
                                    hit = true;
                                }
                            }
                        });
                        if hit {
                            touch.insert(d.name);
                            grew = true;
                        }
                    }
                    if !grew {
                        break;
                    }
                }
                // **A DEVICE BUILTIN ANYWHERE IN THE UNIT ASKS FOR THE MACHINE**,
                // because a program can also reach a device through a memory
                // address no builtin names: e1000-tx-deadline reads the HPET
                // with `peek-32`, and under `Mem` that address is RAM and its
                // clock never moves. A chapter is emitted whole, so a unit that
                // cites one for a drawing function brings its PCI scan along,
                // and gets the machine.
                //
                // `by_reach` is for a platform whose host stops a read or
                // write at an address it does not back (roc-apps framebuffer):
                // there a unit threads the machine only when a chain of names
                // from the opening arrives at a device builtin (`bin/reaches`
                // prints the chain), and a definition the opening cannot reach
                // is written as a crash naming the builtin it reaches. A
                // library has no opening, and every definition counts.
                let mut wired: BTreeMap<Sym, Sym> = BTreeMap::new();
                loop {
                    let mut grew = false;
                    for d in defs {
                        if wired.contains_key(&d.name) {
                            continue;
                        }
                        let mut via = None;
                        d.body.walk(&mut |x| {
                            if let IrExpr::Name(n, _, _) = x {
                                if via.is_none() {
                                    via = if devices.contains(n) { Some(*n) } else { wired.get(n).copied() };
                                }
                            }
                        });
                        if let Some(b) = via {
                            wired.insert(d.name, b);
                            grew = true;
                        }
                    }
                    if !grew {
                        break;
                    }
                }
                let by_name: BTreeMap<Sym, &IrDef> = defs.iter().map(|d| (d.name, d)).collect();
                let reached: std::collections::BTreeSet<Sym> = match syms.find("opening").filter(|o| by_name.contains_key(o)) {
                    Some(open) => {
                        let mut seen = std::collections::BTreeSet::from([open]);
                        let mut stack = vec![open];
                        while let Some(n) = stack.pop() {
                            by_name[&n].body.walk(&mut |x| {
                                if let IrExpr::Name(m, _, _) = x {
                                    if by_name.contains_key(m) && seen.insert(*m) {
                                        stack.push(*m);
                                    }
                                }
                            });
                        }
                        seen
                    }
                    None => by_name.keys().copied().collect(),
                };
                let machine = vm_flags || if by_reach { reached.iter().any(|n| wired.contains_key(n)) } else { !wired.is_empty() };
                // The opening makes the state itself (`opening`), so it stays
                // the app's main rather than becoming a function of the state.
                if !touch.is_empty() {
                    cx.state = if machine { "Machine" } else { "Mem" };
                    if !machine {
                        cx.stubbed = wired;
                    }
                    cx.device_ops = ops;
                    cx.device_defs = touch;
                    if let Some(o) = syms.find("opening") {
                        cx.device_defs.remove(&o);
                    }
                }
            }
        }
        for (td, c) in ch.type_defs.iter().zip(&ch.type_def_chapters) {
            let n = match td {
                TypeDef::Record(n, ..) | TypeDef::Variant(n, ..) | TypeDef::Unit(n, ..) => *n,
            };
            cx.type_module.insert(n, module_slug(c));
        }
        for d in defs {
            cx.def_module.insert(d.name, module_slug(&d.origin));
        }
        // Who mentions whom, over the declared types alone, and then who
        // reaches themselves: one round of closure per type is enough for a
        // chapter's handful, and a fixed point is cheap to spell.
        let mut mentions: BTreeMap<Sym, std::collections::BTreeSet<Sym>> = BTreeMap::new();
        for td in &ch.type_defs {
            let (n, ts) = match td {
                TypeDef::Record(n, _, fields, _, _) => (*n, fields.iter().map(|f| f.type_expr.clone()).collect::<Vec<_>>()),
                TypeDef::Variant(n, _, ctors, _) => (*n, ctors.iter().flat_map(|c| c.fields.clone()).collect()),
                TypeDef::Unit(n, t, _) => (*n, vec![t.clone()]),
            };
            let mut out = std::collections::BTreeSet::new();
            for t in &ts {
                named_types(t, &mut out);
            }
            out.retain(|m| cx.type_module.contains_key(m));
            if ts.iter().any(holds_fun) {
                cx.fun_holding.insert(n);
            }
            mentions.insert(n, out);
        }
        loop {
            let mut grew = false;
            for (n, ms) in mentions.clone() {
                for m in &ms {
                    for far in mentions.get(m).cloned().unwrap_or_default() {
                        if mentions.get_mut(&n).is_some_and(|set| set.insert(far)) {
                            grew = true;
                        }
                    }
                }
            }
            if !grew {
                break;
            }
        }
        cx.recursive = mentions.iter().filter(|(n, ms)| ms.contains(n)).map(|(n, _)| *n).collect();
        cx.nominal = cx.recursive.clone();
        for td in &ch.type_defs {
            // Not a record with type parameters: its equality would need a
            // `where` clause per parameter, which `methods` does not write, and a
            // generic record is not what two same-shaped Codex types collide on.
            if let TypeDef::Record(n, ps, fields, _, _) = td {
                if !fields.is_empty() && ps.is_empty() {
                    cx.nominal.insert(*n);
                }
            }
        }
        let direct = cx.fun_holding.clone();
        cx.fun_holding.extend(mentions.iter().filter(|(_, ms)| ms.iter().any(|m| direct.contains(m))).map(|(n, _)| *n));
        for d in defs {
            if let Some(t) = syms.text(d.name).strip_prefix("__eq_") {
                if let Some(n) = syms.find(t).filter(|n| cx.type_module.contains_key(n)) {
                    cx.derived_eq.insert(n, d.name);
                }
            }
        }
        cx.bang_defs = defs.iter().filter(|d| cx.takes_bang(d)).map(|d| d.name).collect();
        cx
    }

    /// A name from module `module`, as seen from the module being emitted:
    /// bare at home, `Module.name` elsewhere, and the import is remembered.
    fn qualified(&mut self, module: &str, name: String) -> String {
        if module.is_empty() || module == self.current {
            return name;
        }
        self.imports.insert(module_ident(module));
        format!("{}.{name}", module_ident(module))
    }

    /// A definition's name as a reference.
    fn def_ref(&mut self, n: Sym) -> Result<String, String> {
        let m = self.def_module.get(&n).cloned().unwrap_or_default();
        let mut id = self.ident(n)?;
        // An effectful definition is named with `!` (`def`).
        if self.bang_defs.contains(&n) {
            id.push('!');
        }
        Ok(self.qualified(&m, id))
    }

    /// A declared type's name as a reference. `Maybe` undeclared is the
    /// Prelude's, in the module layout.
    ///
    /// **ALWAYS QUALIFIED, EVEN AT HOME.** Chapter Cat declares a type named
    /// Cat, and inside `Cat :: [].{ ... }` a bare `Cat` is the module's own
    /// void type, not the alias nested in it: every definition returning a
    /// Cat then returns the empty type, and every unit that builds a world
    /// crashes at compile time. `Cat.Cat` resolves to the alias from inside
    /// and outside alike.
    fn type_ref(&mut self, n: Sym) -> String {
        let name = type_name(self.syms.text(n));
        let m = match self.type_module.get(&n) {
            Some(m) => m.clone(),
            None if n == self.maybe => "Prelude".to_string(),
            None => String::new(),
        };
        if m.is_empty() {
            return name;
        }
        // The app is not a type module: its own types are bare, since there
        // is no `App.` to qualify them by. A chapter module's are qualified
        // even at home (Cat.Cat, above).
        if m == self.current && m == self.app {
            return name;
        }
        if m != self.current {
            self.imports.insert(module_ident(&m));
        }
        format!("{}.{name}", module_ident(&m))
    }

    // ---- names ----------------------------------------------------------

    fn ident(&self, n: Sym) -> Result<String, String> {
        ident_text(self.syms.text(n))
    }

    /// A local's spelling. Roc has no shadowing: a parameter named like a
    /// top-level definition is a duplicate definition, so such a local gets
    /// a trailing underscore. Inside its scope every reference to the name
    /// is the local's, which is what lexical scope says.
    fn local(&self, n: Sym) -> Result<String, String> {
        let id = self.ident(n)?;
        // In the module layout another chapter's definition is reached as
        // `Module.name`, so only a definition of THIS module can collide --
        // and a module's text must not depend on which spec is attached.
        let collides = self.arity.contains_key(&n) && self.def_module.get(&n).is_some_and(|m| *m == self.current);
        // A local spelled like the threaded state's own names (`mem`,
        // `machine2`) would shadow them, so it takes the underscore too.
        let base = self.dev_base();
        let state_like = id.starts_with(base) && id[base.len()..].chars().all(|c| c.is_ascii_digit());
        Ok(if collides || state_like { format!("{id}_") } else { id })
    }

    fn tag(&self, n: Sym) -> Result<String, String> {
        let t = self.syms.text(n);
        if t.starts_with(|c: char| c.is_ascii_uppercase()) && t.chars().all(|c| c.is_ascii_alphanumeric()) {
            Ok(t.to_string())
        } else {
            Err(format!("constructor `{t}` is not a Roc tag name"))
        }
    }

    // ---- types ----------------------------------------------------------

    /// The integer and real types this unit is spelled in (see `wgsl`).
    fn int(&self) -> &'static str {
        if self.wgsl { "I32" } else { "I64" }
    }
    fn real(&self) -> &'static str {
        if self.wgsl { "F32" } else { "F64" }
    }
    /// The unsigned type of the same width, for bit patterns.
    fn uint(&self) -> &'static str {
        if self.wgsl { "U32" } else { "U64" }
    }

    fn ty(&mut self, t: &Ty) -> Result<String, String> {
        Ok(match t {
            Ty::Integer(..) => self.int().into(),
            // A Codex Char is its code, as its own type (see `roc_text`).
            Ty::Char => {
                self.imports.insert("CceChar".into());
                "CceChar".into()
            }
            Ty::Real(RealWidth::F64, _) => self.real().into(),
            // `Real approximate`, whatever its overflow mode: the mode is on
            // the operations (`binary`), not the type.
            Ty::Real(RealWidth::F32, _) => "F32".into(),
            Ty::Text => {
                self.imports.insert("CceText".into());
                "CceText".into()
            }
            Ty::Boolean => "Bool".into(),
            Ty::Nothing => "{}".into(),
            Ty::Unit(n, _) => self.type_ref(*n),
            Ty::List(e) => format!("List({})", self.ty(e)?),
            Ty::Fun(..) => {
                let (ps, r) = self.fun_parts(t)?;
                format!("({} {r})", ps.join(", "))
            }
            Ty::Var(id) => {
                let next = self.tvars.len();
                self.tvars
                    .entry(*id)
                    .or_insert_with(|| ((b'a' + (next % 26) as u8) as char).to_string())
                    .clone()
            }
            Ty::ForAll(_, b) | Ty::ForAllEff(_, b) | Ty::Linear(b) => self.ty(b)?,
            // `list_versions`' copy-out tuple.
            Ty::Constructed(n, a) if self.syms.text(*n) == crate::list_versions::TUPLE => {
                let args: Result<Vec<_>, _> = a.iter().map(|x| self.ty(x)).collect();
                format!("({})", args?.join(", "))
            }
            Ty::Sum(n, a) | Ty::Record(n, a) | Ty::Constructed(n, a) => {
                let name = self.type_ref(*n);
                if a.is_empty() {
                    name
                } else {
                    let args: Result<Vec<_>, _> = a.iter().map(|x| self.ty(x)).collect();
                    format!("{name}({})", args?.join(", "))
                }
            }
            other => return Err(format!("type {}", crate::ir_text::render_ty(self.syms, other))),
        })
    }

    /// A curried `(fn a (fn b c))` is Roc's `a, b -> c`: Codex functions are
    /// written saturated, so the whole chain is one signature.
    fn fun_parts(&mut self, t: &Ty) -> Result<(Vec<String>, String), String> {
        let mut ps = Vec::new();
        let mut eff = false;
        let mut cur = t;
        loop {
            match cur {
                Ty::Fun(p, row, r) => {
                    eff |= !row.labels.is_empty();
                    ps.push(self.ty(p)?);
                    cur = r;
                }
                Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => cur = b,
                _ => break,
            }
        }
        let r = self.ty(cur)?;
        Ok((ps, if eff { format!("=> {r}") } else { format!("-> {r}") }))
    }

    /// A definition's signature: `k` parameters peel `k` arrows.
    fn signature(&mut self, d: &IrDef) -> Result<String, String> {
        let (ps, r, eff) = self.arrows(d)?;
        // **AN EFFECTFUL FUNCTION'S ARROW IS `=>`.** Roc marks the effect on
        // the type, as Codex marks it on the row; a `[Console] Nothing`
        // annotated `->` is a type error at every call (scope-console).
        let arrow = if eff { "=>" } else { "->" };
        let sig = if ps.is_empty() { r } else { format!("{} {arrow} {}", ps.join(", "), r) };
        let wants = self.eq_wants(d)?;
        Ok(if wants.is_empty() { sig } else { format!("{sig} where [{}]", wants.join(", ")) })
    }

    /// A `[Device]` definition's signature: the device first, and the pair
    /// last. The arrow is `=>` when an effect the state does not answer is
    /// left over (a definition that reads the disk and prints), and always
    /// when the state is memory or the machine, whose doors may be the host's.
    /// A GPU kernel's Device is plain arithmetic, called from pure code.
    fn device_signature(&mut self, d: &IrDef) -> Result<String, String> {
        let (ps, r, eff) = self.arrows(d)?;
        let mut all = vec![format!("{s}.{s}", s = self.state)];
        all.extend(ps);
        let arrow = if eff || self.state != "Device" { "=>" } else { "->" };
        let sig = format!("{} {arrow} ({s}.{s}, {r})", all.join(", "), s = self.state);
        let wants = self.eq_wants(d)?;
        Ok(if wants.is_empty() { sig } else { format!("{sig} where [{}]", wants.join(", ")) })
    }

    /// `k` parameters peel `k` arrows: the parameter types, the result, and
    /// whether any of those arrows performs an effect Roc must see. An effect
    /// the threaded state answers is not one: the state carries it.
    fn arrows(&mut self, d: &IrDef) -> Result<(Vec<String>, String, bool), String> {
        self.tvars.clear();
        let eff = self.effect_left(d);
        let mut cur = &d.ty;
        let mut ps = Vec::new();
        for _ in 0..d.params.len() {
            loop {
                match cur {
                    Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => cur = b,
                    _ => break,
                }
            }
            match cur {
                Ty::Fun(p, _, r) => {
                    ps.push(self.ty(p)?);
                    cur = r;
                }
                other => {
                    return Err(format!(
                        "`{}` has {} parameters but its type is {}",
                        self.syms.text(d.name),
                        d.params.len(),
                        crate::ir_text::render_ty(self.syms, other)
                    ))
                }
            }
        }
        // A nullary `[Device] T`, or `[Device.Block] T` under the machine, is
        // effectful in its type; the state's signature carries the effect, so
        // the result is the T.
        let r = match cur {
            Ty::Effectful(names, _, inner) if self.state_carries(cur, names) => self.ty(inner)?,
            _ => self.ty(cur)?,
        };
        Ok((ps, r, eff))
    }

    /// Whether any of a definition's `k` arrows, or the effectful result a
    /// state carries, leaves an effect the threaded state does not answer.
    fn effect_left(&self, d: &IrDef) -> bool {
        let mut cur = &d.ty;
        let mut eff = false;
        for _ in 0..d.params.len() {
            while let Ty::ForAll(_, b) | Ty::ForAllEff(_, b) = cur {
                cur = b;
            }
            let Ty::Fun(_, row, r) = cur else { return eff };
            eff |= row.labels.iter().any(|(l, _)| !self.threads(l));
            cur = r;
        }
        if let Ty::Effectful(names, _, _) = cur {
            if self.state_carries(cur, names) {
                eff |= names.iter().any(|n| !self.threads(self.syms.text(*n)));
            }
        }
        eff
    }

    /// A nullary `[Device] T`, or `[Device.Block] T` under the machine: the
    /// state's signature carries the effect.
    fn state_carries(&self, t: &Ty, names: &[Sym]) -> bool {
        self.has_device(t) || names.iter().any(|n| self.threads(self.syms.text(*n)))
    }

    /// Whether a definition's signature takes `=>`, as `signature` and
    /// `device_signature` write it.
    fn takes_bang(&self, d: &IrDef) -> bool {
        if self.device_defs.contains(&d.name) {
            self.effect_left(d) || self.state != "Device"
        } else {
            !d.params.is_empty() && self.effect_left(d)
        }
    }

    /// Whether the threaded state answers an effect: `Device` for a GPU
    /// kernel; for the machine, the `Device.` family (`Device.Block`,
    /// `Device.Port`) and `Capability`, whose builtins read and write the
    /// process table it keeps. `Mem` carries the same rows: a unit runs
    /// without the machine only when its opening reaches no device builtin, so
    /// under `Mem` such a row is declared on a definition that never performs
    /// it, or on one written as a crash (`stubbed`).
    fn threads(&self, label: &str) -> bool {
        match self.state {
            "Device" => label == "Device",
            "Machine" | "Mem" => {
                label.starts_with("Device.") || label == "Capability" || label.starts_with("Network.") || label.starts_with("Gpu")
            }
            _ => false,
        }
    }

    /// **`==` ON A TYPE VARIABLE NEEDS A `where` CLAUSE.** Roc's equality
    /// is the `is_eq` method of the left operand's type; a type variable
    /// has none unless the signature requires one (static-dispatch.md,
    /// "Where Clauses"). The derived equality on the prelude's tuples
    /// compares fields of type `a`.
    fn eq_wants(&mut self, d: &IrDef) -> Result<Vec<String>, String> {
        let mut eq_vars: Vec<u32> = Vec::new();
        d.body.walk(&mut |x| {
            if let IrExpr::Binary(IrBinOp::Eq | IrBinOp::NotEq, l, _, _, _) = x {
                let mut t = l.ty();
                while let Ty::ForAll(_, b) | Ty::ForAllEff(_, b) = t {
                    t = *b;
                }
                if let Ty::Var(id) = t {
                    if !eq_vars.contains(&id) {
                        eq_vars.push(id);
                    }
                }
            }
        });
        let mut wants: Vec<String> = Vec::new();
        for id in eq_vars {
            let v = self.ty(&Ty::Var(id))?;
            wants.push(format!("{v}.is_eq : {v}, {v} -> Bool"));
        }
        Ok(wants)
    }

    /// Whether a type carries the Device effect: on an arrow's row, or as
    /// an effectful nullary's label.
    fn has_device(&self, t: &Ty) -> bool {
        let mut cur = t;
        loop {
            match cur {
                Ty::ForAll(_, b) | Ty::ForAllEff(_, b) | Ty::Linear(b) => cur = b,
                Ty::Fun(_, row, r) => {
                    if row.labels.iter().any(|(l, _)| l == "Device") {
                        return true;
                    }
                    cur = r;
                }
                Ty::Effectful(names, _, _) => return names.iter().any(|n| self.syms.text(*n) == "Device"),
                _ => return false,
            }
        }
    }

    fn texpr(&mut self, t: &TypeExpr) -> Result<String, String> {
        Ok(match t {
            TypeExpr::Named(n, _) => match self.syms.text(*n) {
                "Real" => self.real().into(),
                "Integer" => self.int().into(),
                "Char" => {
                    self.imports.insert("CceChar".into());
                    "CceChar".into()
                }
                "Text" => {
                    self.imports.insert("CceText".into());
                    "CceText".into()
                }
                "Boolean" => "Bool".into(),
                "Nothing" => "{}".into(),
                s if s.starts_with(|c: char| c.is_ascii_lowercase()) => s.to_string(),
                _ => self.type_ref(*n),
            },
            // `Real approximate saturating`: qualifiers, not arguments
            // (`resolve-real-quals`); only the width shows in Roc.
            TypeExpr::App(f, args, _)
                if matches!(&**f, TypeExpr::Named(n, _) if self.syms.text(*n) == "Real")
                    && args.iter().all(|a| {
                        matches!(a, TypeExpr::Named(w, _) if matches!(self.syms.text(*w), "approximate" | "trapping" | "saturating"))
                    }) =>
            {
                let f32 = args.iter().any(|a| matches!(a, TypeExpr::Named(w, _) if self.syms.text(*w) == "approximate"));
                if f32 { "F32".into() } else { self.real().into() }
            }
            TypeExpr::App(f, args, _) => {
                let TypeExpr::Named(n, _) = &**f else {
                    return Err("a type applied to a non-name".into());
                };
                let head = match self.syms.text(*n) {
                    "List" => "List".to_string(),
                    _ => self.type_ref(*n),
                };
                let mut xs = Vec::new();
                for a in args {
                    xs.push(self.texpr(a)?);
                }
                format!("{head}({})", xs.join(", "))
            }
            TypeExpr::Fun(..) => {
                let mut ps = Vec::new();
                let mut cur = t;
                while let TypeExpr::Fun(a, b, _) = cur {
                    ps.push(self.texpr(a)?);
                    cur = b;
                }
                format!("({} -> {})", ps.join(", "), self.texpr(cur)?)
            }
            // `Integer between lo and hi wrapping`: the Roc type is the
            // integer; the mode is on every node's type and `binary` reads it.
            TypeExpr::BoundedInt(inner, _, _, _, _) => self.texpr(inner)?,
            other => return Err(format!("a type form outside the subset in a type definition: {other:?}").chars().take(160).collect()),
        })
    }

    /// The type of a derived `__eq_` definition Roc cannot write, because the
    /// type holds a function.
    fn unwritable_eq(&self, d: Sym) -> Option<Sym> {
        self.derived_eq.iter().find(|(t, e)| **e == d && self.fun_holding.contains(*t)).map(|(t, _)| *t)
    }

    /// **A NOMINAL TYPE HAS NO STRUCTURAL `==`.** An alias is compared
    /// field by field; a `:=` type is asked for its `is_eq` method, and a
    /// list or record holding one is compared through that. Codex derives
    /// the equality already, so the nominal declaration carries it as a
    /// forwarder and `==` works on the type wherever it appears
    /// (codex/test's shell-build-keep).
    fn methods(&mut self, td: &TypeDef, base: usize) -> Result<String, String> {
        let n = match td {
            TypeDef::Record(n, ..) | TypeDef::Variant(n, ..) | TypeDef::Unit(n, ..) => *n,
        };
        if !self.nominal.contains(&n) || self.fun_holding.contains(&n) {
            return Ok(String::new());
        }
        let t = "\t".repeat(base + 1);
        let ty = self.type_ref(n);
        // Codex derives an equality for a type its programs compare, and
        // that one is the method. A type only compared INSIDE another's
        // equality has none derived, so one is written here from the
        // shape: `CborMapEntry` holds two `CborValue`s and nothing
        // compares it directly (codex/test's lib/cbor-test).
        if let Some(eq) = self.derived_eq.get(&n).copied() {
            if let Some(d) = self.defs.iter().find(|d| d.name == eq) {
                let sig = self.signature(d)?;
                let call = self.def_ref(eq)?;
                return Ok(format!(".{{\n{t}is_eq : {sig}\n{t}is_eq = |a, b| {call}(a, b)\n{}}}", "\t".repeat(base)));
            }
        }
        let body = match td {
            TypeDef::Record(_, ps, fields, _, _) if ps.is_empty() && !fields.is_empty() => {
                let mut parts = Vec::new();
                for f in fields {
                    let f = self.ident(f.name)?;
                    parts.push(format!("a.{f} == b.{f}"));
                }
                parts.join(" and ")
            }
            TypeDef::Variant(_, ps, ctors, _) if ps.is_empty() && !ctors.is_empty() => {
                let mut arms = Vec::new();
                for c in ctors {
                    let tag = self.tag(c.name)?;
                    if c.fields.is_empty() {
                        arms.push(format!("{t}\t{tag} => (match b {{ {tag} => True\n{t}\t\t_ => False }})"));
                    } else {
                        let xs: Vec<String> = (0..c.fields.len()).map(|i| format!("x{i}")).collect();
                        let ys: Vec<String> = (0..c.fields.len()).map(|i| format!("y{i}")).collect();
                        let cmp: Vec<String> = xs.iter().zip(&ys).map(|(x, y)| format!("{x} == {y}")).collect();
                        arms.push(format!(
                            "{t}\t{tag}({}) => (match b {{ {tag}({}) => {}\n{t}\t\t_ => False }})",
                            xs.join(", "),
                            ys.join(", "),
                            cmp.join(" and ")
                        ));
                    }
                }
                format!("match a {{\n{}\n{t}}}", arms.join("\n"))
            }
            _ => return Ok(String::new()),
        };
        Ok(format!(
            ".{{\n{t}is_eq : {ty}, {ty} -> Bool\n{t}is_eq = |a, b| {body}\n{}}}",
            "\t".repeat(base)
        ))
    }

    /// `:` for a plain alias, `:=` for one that stands on a cycle.
    fn colon(&self, n: Sym) -> &'static str {
        if self.nominal.contains(&n) { ":=" } else { ":" }
    }

    fn type_def(&mut self, td: &TypeDef, base: usize) -> Result<String, String> {
        let syms = self.syms;
        let head = |n: Sym, ps: &[Sym]| -> Result<String, String> {
            let name = type_name(syms.text(n));
            if ps.is_empty() {
                return Ok(name);
            }
            let ps: Vec<&str> = ps.iter().map(|p| syms.text(*p)).collect();
            Ok(format!("{name}({})", ps.join(", ")))
        };
        let tabs = "\t".repeat(base);
        Ok(match td {
            TypeDef::Record(n, ps, fields, _, _) => {
                let mut fs = Vec::new();
                for f in fields {
                    let mut ty = self.texpr(&f.type_expr)?;
                    // A class dictionary's `__super-<S> : <S>Dict` is the
                    // superclass's dictionary AT THE SAME TYPE. Upstream writes
                    // it bare (desugar.rs `synth_class_type_defs`); Roc reads a
                    // bare parameterised alias as free, for each use to fix
                    // apart, so the parameter is written.
                    if syms.text(f.name).starts_with("__super-") && matches!(f.type_expr, TypeExpr::Named(..)) && !ps.is_empty() {
                        let ps: Vec<&str> = ps.iter().map(|p| syms.text(*p)).collect();
                        ty = format!("{ty}({})", ps.join(", "));
                    }
                    fs.push(format!("{} : {}", self.ident(f.name)?, ty));
                }
                let col = self.colon(*n);
                let body = if fs.is_empty() { "{}".to_string() } else { format!("{{ {} }}", fs.join(", ")) };
                format!("{tabs}{} {col} {body}{}\n", head(*n, ps)?, self.methods(td, base)?)
            }
            TypeDef::Variant(n, ps, ctors, _) => {
                let mut cs = Vec::new();
                for c in ctors {
                    if !c.return_type.is_empty() {
                        return Err(format!("constructor `{}` declares a return type", self.syms.text(c.name)));
                    }
                    let tag = self.tag(c.name)?;
                    if c.fields.is_empty() {
                        cs.push(tag);
                    } else {
                        let mut fs = Vec::new();
                        for f in &c.fields {
                            fs.push(self.texpr(f)?);
                        }
                        cs.push(format!("{tag}({})", fs.join(", ")));
                    }
                }
                format!(
                    "{tabs}{} {} [{}]{}\n",
                    head(*n, ps)?,
                    self.colon(*n),
                    cs.join(", "),
                    self.methods(td, base)?
                )
            }
            // **A UNIT IS ITS BASE NUMBER.** Lowering elides a unit's
            // constructor and keeps the unit on the value, and the desugarer
            // writes each family member's constructor and extractor as plain
            // arithmetic, so at run time a `Duration` is the Integer it wraps.
            TypeDef::Unit(n, base, _) => format!("{tabs}{} : {}\n", head(*n, &[])?, self.texpr(base)?),
        })
    }

    // ---- definitions ----------------------------------------------------

    /// A definition, or the line that says a data table was left to a baker.
    ///
    /// **A DATA TABLE IS NOT EMITTED, AND THE OMISSION IS WRITTEN DOWN.**
    /// A definition, whole; a data table of thousands of literals is emitted
    /// as the literal it is, since the nightly's checker is linear in them.
    /// Whole mode's `def`: the definition as written, else its stub, else
    /// nothing. A failure is recorded for the next round and the state the
    /// attempt left behind is put back.
    fn def_or_stub(&mut self, d: &IrDef, base: usize) -> Option<String> {
        match self.fates.get(&d.name).cloned() {
            Some(Fate::Omit(_)) => return None,
            Some(Fate::Stub(why)) => return self.stub(d, base, &why),
            None => {}
        }
        let (locals, imports) = (self.locals.len(), self.imports.clone());
        let written = self.def(d, base).and_then(|t| match self.undeclared.iter().find(|n| mentions(&t, n)) {
            Some(n) => Err(format!("it uses class dictionary `{n}` as a value, and no Roc type holds it (UNSUPPORTED_FREE_BINDER)")),
            None => Ok(t),
        });
        match written {
            Ok(t) => Some(t),
            Err(why) => {
                self.locals.truncate(locals);
                self.imports = imports;
                self.dev = None;
                self.failed.push((d.name, why.clone()));
                if d.params.is_empty() { None } else { self.stub(d, base, &why) }
            }
        }
    }

    /// `name = |_, ...| crash("...")`, under its signature when that can be
    /// written and bare when it cannot.
    fn stub(&mut self, d: &IrDef, base: usize, why: &str) -> Option<String> {
        if d.params.is_empty() {
            return None;
        }
        let bang = if self.bang_defs.contains(&d.name) { "!" } else { "" };
        let name = format!("{}{bang}", self.ident(d.name).ok()?);
        let dev = self.device_defs.contains(&d.name);
        let imports = self.imports.clone();
        let sig = if dev { self.device_signature(d) } else { self.signature(d) };
        let blanks = vec!["_"; d.params.len() + usize::from(dev)].join(", ");
        let msg = format!("rocemit could not write `{}`: {why}", self.syms.text(d.name)).replace(['"', '\\', '$'], "'");
        let tabs = "\t".repeat(base);
        let sig = sig.and_then(|t| if self.undeclared.iter().any(|n| mentions(&t, n)) { Err(String::new()) } else { Ok(t) });
        let head = match sig {
            Ok(sig) => format!("{tabs}{name} : {sig}\n"),
            Err(_) => {
                self.imports = imports;
                String::new()
            }
        };
        if dev {
            self.imports.insert(self.state.into());
        }
        Some(format!("{head}{tabs}{name} = |{blanks}| crash(\"{msg}\")\n"))
    }

    fn def(&mut self, d: &IrDef, base: usize) -> Result<String, String> {
        self.heap_live = self.by_closure() && self.device_defs.contains(&d.name);
        self.tmp_n = 0;
        // Roc spells an effectful function's name with `!` (`def_ref` agrees).
        let bang = if self.bang_defs.contains(&d.name) { "!" } else { "" };
        let name = format!("{}{bang}", self.ident(d.name)?);
        let sig = self.signature(d)?;
        let mark = self.locals.len();
        let mut ps = Vec::new();
        for p in &d.params {
            self.locals.push(p.name);
            ps.push(self.binder(p.name, &[&d.body])?);
        }
        let tabs = "\t".repeat(base);
        if self.device_defs.contains(&d.name) {
            self.imports.insert(self.state.into());
            // **A DEFINITION THE OPENING CANNOT REACH MAY NAME A DEVICE THE
            // STATE DOES NOT HAVE.** `Mem` has no door for a port or a sector,
            // so the body is a crash naming the device builtin it reaches, under
            // the signature a caller would see.
            if let Some(b) = self.stubbed.get(&d.name).copied() {
                self.locals.truncate(mark);
                let sig = self.device_signature(d)?;
                let blanks = vec!["_"; d.params.len() + 1].join(", ");
                let what = format!(
                    "`{}` reaches `{}`, a device builtin this program's opening never calls, and the program runs without the machine",
                    self.syms.text(d.name),
                    self.syms.text(b)
                );
                return Ok(format!("{tabs}{name} : {sig}\n{tabs}{name} = |{blanks}| crash(\"{what}\")\n"));
            }
            for p in &d.params {
                self.no_dev_name(p.name)?;
            }
            self.dev_n = 0;
            self.dev = Some(self.dev_base().to_string());
            let sig = self.device_signature(d)?;
            let body = self.eff_expr(&d.body, base)?;
            self.dev = None;
            self.locals.truncate(mark);
            let mut all = vec![self.dev_base().to_string()];
            all.extend(ps);
            return Ok(format!("{tabs}{name} : {sig}\n{tabs}{name} = |{}| {body}\n", all.join(", ")));
        }
        if let Some(body) = in_roc(&module_slug(&d.origin), self.syms.text(d.name), &ps, self.real()) {
            self.locals.truncate(mark);
            return Ok(format!("{tabs}{name} : {sig}\n{tabs}{name} = {body}\n"));
        }
        // **A RIGHT FOLD IS EMITTED AS AN ACCUMULATOR LOOP.** Codex builds a
        // list by `x & f rest`: the recursive call is the right operand of
        // an append, and each level copies everything below it, so a
        // 2,430-element list costs 1.7 seconds in Roc where an accumulator
        // costs milliseconds (measured, roc-apps probe/cons). The shape is
        // recognised, not guessed: every recursive call sits as the right
        // operand of an append at a leaf of the if-tree, and nowhere else.
        //
        // **SO IS A LIST BUILT BY PUSHING ONTO A RECURSIVE CALL**, `list-push
        // (f rest) x`. That recursion is as deep as the list is long, and
        // GlyphRasterizer's 4x4 supersampled glyph buffer overflows a browser's
        // stack with it. The loop gathers the pushed elements outermost first,
        // so a base case takes them back to front (`Prelude.push_backwards`).
        let push_fold = !ps.is_empty() && is_push_fold(&d.body, d.name, &self.push_syms());
        let out = if !ps.is_empty() && (push_fold || is_right_fold(&d.body, d.name)) {
            let acc = self.syms.find("acc").filter(|a| self.locals.contains(a)).map_or("acc", |_| "acc_");
            let helper = format!("{}_acc{bang}", self.ident(d.name)?);
            // `fun_parts` gives the result with its arrow ("-> List(a)"),
            // which is what the helper's signature ends with.
            let (params, ret) = self.fun_parts(&d.ty)?;
            let _ = params;
            let bare = ret.trim_start_matches(['-', '=', '>', ' ']).to_string();
            let mut hsig: Vec<String> = Vec::new();
            for p in &d.params {
                hsig.push(self.ty(&p.ty)?);
            }
            hsig.push(bare.clone());
            self.fold = Some(Fold { name: d.name, helper: helper.clone(), acc: acc.to_string(), push: push_fold });
            let body = self.expr(&d.body, base)?;
            self.fold = None;
            let why = if push_fold {
                "pushing onto a recursive call; emitted as an accumulator loop, which needs no stack as deep as the list is long"
            } else {
                "appending a recursive call; emitted as an accumulator loop, which is linear where the direct shape is quadratic"
            };
            format!(
                "{tabs}# {name} builds its list by {why}.\n\
                 {tabs}{name} : {sig}\n{tabs}{name} = |{ps}| {helper}({ps}, [])\n\n\
                 {tabs}{helper} : {hsig} {ret}\n{tabs}{helper} = |{ps}, {acc}| {body}\n",
                ps = ps.join(", "),
                hsig = hsig.join(", ")
            )
        } else {
            let body = self.expr(&d.body, base)?;
            if ps.is_empty() {
                format!("{tabs}{name} : {sig}\n{tabs}{name} = {body}\n")
            } else {
                format!("{tabs}{name} : {sig}\n{tabs}{name} = |{}| {body}\n", ps.join(", "))
            }
        };
        self.locals.truncate(mark);
        Ok(out)
    }

    /// The effects an opening declares, as x86's boot reads them off its type
    /// (`manifest-opening-effects`): the rows of its arrows, then an effectful
    /// result's names, each once.
    fn opening_effects(&self, t: &Ty) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        let mut cur = t;
        loop {
            let names: Vec<&str> = match cur {
                Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => {
                    cur = b;
                    continue;
                }
                Ty::Fun(_, row, r) => {
                    cur = r;
                    row.labels.iter().map(|(l, _)| l.as_str()).collect()
                }
                Ty::Effectful(names, _, inner) => {
                    cur = inner;
                    names.iter().map(|n| self.syms.text(*n)).collect()
                }
                _ => break,
            };
            for n in names {
                if !out.iter().any(|o| o == n) {
                    out.push(n.to_string());
                }
            }
        }
        out
    }

    /// `opening : [Console] Nothing = act ...` is `main!`.
    fn opening(&mut self, d: &IrDef) -> Result<String, String> {
        if !d.params.is_empty() {
            return Err("opening takes parameters".into());
        }
        self.tmp_n = 0;
        // **THE MACHINE RUNS ONE UNSCOPED PROCESS.** x86 stores the opening's
        // FileSystem and Network scopes as the boot process's before it runs,
        // and `process-get-scope` answers them; the machine answers the empty
        // scope, which admits every path, so an opening that declares one is
        // refused rather than run with its scope dropped.
        if self.state == "Machine" {
            if let Ty::Effectful(names, scopes, _) = &d.ty {
                if let Some((n, s)) = names.iter().zip(scopes).find(|(_, s)| !s.is_empty()) {
                    return Err(format!("an opening scoped to {} \"{s}\"", self.syms.text(*n)));
                }
            }
        }
        let mark = self.locals.len();
        // `args` is read only to keep the memory out of the compiler's
        // reach (see `Mem.new`); every other opening leaves it unused.
        let memory_first = self.by_closure() && self.has_effect(&d.body);
        let mut out = String::from(if memory_first { "main! = |args| {\n" } else { "main! = |_args| {\n" });
        // **THE OPENING IS WHERE THE ADDRESS SPACE COMES FROM.** Every
        // definition that pokes takes the memory and answers it back; the
        // program's root is the one place that has to make one.
        let memory = memory_first;
        self.heap_live = memory;
        if memory {
            self.imports.insert(self.state.into());
            self.dev_n = 0;
            self.dev = Some(self.dev_base().to_string());
            // The machine comes from the command line, as codex-vm's devices
            // do, and from the effects the opening declares, which x86's boot
            // writes into the boot process's capability word; an address space
            // alone needs nothing from either.
            let make = if self.state == "Machine" {
                let effs: Vec<String> = self.opening_effects(&d.ty).iter().map(|e| format!("\"{e}\"")).collect();
                format!("Machine.boot!(args, [{}])", effs.join(", "))
            } else {
                "Mem.new(U64.to_i64_wrap(List.len(args)))".to_string()
            };
            out.push_str(&format!("\t{} = {make}\n", self.dev_base()));
        }
        // **AN OPENING MAY BE WRAPPED IN LETS**, and upstream runs the act
        // inside them; the bindings are main!'s own.
        let mut body = &d.body;
        while let IrExpr::Let(n, _, v, inner, _) = body {
            let (lines, v) = self.hoisting(v, 1)?;
            for l in lines {
                out.push_str(&format!("\t{l}\n"));
            }
            self.locals.push(*n);
            out.push_str(&format!("\t{} = {v}\n", self.binder(*n, &[inner])?));
            body = inner;
        }
        // **AN OPENING THAT IS A VALUE IS PRINTED**, which is what the
        // driver does with it and what every verdict in codex/test records.
        if !matches!(body, IrExpr::Act(..)) {
            let (lines, x) = self.hoisting(body, 1)?;
            for l in lines {
                out.push_str(&format!("\t{l}\n"));
            }
            let text = match strip_unit(&body.ty()).clone() {
                Ty::Text => {
                    self.uses_text = true;
                    self.imports.insert("CceText".into());
                    format!("CceText.printed({x})")
                }
                Ty::Integer(..) => format!("I64.to_str({x})"),
                other => {
                    return Err(format!(
                        "an opening of type {}",
                        crate::ir_text::render_ty(self.syms, &other)
                    ))
                }
            };
            self.uses_line = true;
            out.push_str(&format!("\tline!({text})\n"));
            self.halt(&mut out, memory);
            out.push_str("\tOk({})\n}\n");
            self.locals.truncate(mark);
            self.dev = None;
            return Ok(seal_state(out, memory, self.dev_base(), self.dev_n));
        }
        let IrExpr::Act(stmts, _, _) = body else { unreachable!() };
        for (i, s) in stmts.iter().enumerate() {
            match s {
                IrActStmt::Exec(e, _) => {
                    let ty = strip_unit(&e.ty()).clone();
                    let (lines, e) = self.hoisting(e, 1)?;
                    for l in lines {
                        out.push_str(&format!("\t{l}\n"));
                    }
                    // **AN ACT'S LAST VALUE IS THE OPENING'S**, and it is
                    // printed like a value opening's: `opening : [Console]
                    // Integer` ends `0`, and its verdict ends with that 0.
                    let last = i + 1 == stmts.len();
                    match ty {
                        Ty::Integer(..) if last => {
                            self.uses_line = true;
                            out.push_str(&format!("\tline!(I64.to_str({e}))\n"));
                        }
                        Ty::Text if last => {
                            self.uses_line = true;
                            self.uses_text = true;
                            self.imports.insert("CceText".into());
                            out.push_str(&format!("\tline!(CceText.printed({e}))\n"));
                        }
                        Ty::Boolean | Ty::Real(..) if last => {
                            return Err(format!("an opening of type {}", crate::ir_text::render_ty(self.syms, &ty)));
                        }
                        _ => out.push_str(&format!("\t{e}\n")),
                    }
                }
                IrActStmt::Bind(n, _, e, _) => {
                    let (lines, e) = self.hoisting(e, 1)?;
                    for l in lines {
                        out.push_str(&format!("\t{l}\n"));
                    }
                    self.locals.push(*n);
                    let rest: Vec<&IrExpr> = stmts[i + 1..].iter().map(|s| s.expr()).collect();
                    out.push_str(&format!("\t{} = {e}\n", self.binder(*n, &rest)?));
                }
            }
        }
        self.locals.truncate(mark);
        self.halt(&mut out, memory);
        self.dev = None;
        out.push_str("\tOk({})\n}\n");
        Ok(seal_state(out, memory, self.dev_base(), self.dev_n))
    }

    /// **THE LAST MACHINE GOES TO `halt!`**, where a platform that shows the
    /// screen reads the framebuffer the run left; elsewhere it does nothing.
    fn halt(&self, out: &mut String, memory: bool) {
        if memory && self.state == "Machine" {
            if let Some(m) = &self.dev {
                out.push_str(&format!("\tMachine.halt!({m})\n"));
            }
        }
    }

    // ---- the Device effect -----------------------------------------------

    /// Whether an expression performs the Device effect: an act, a call of
    /// an operation or of a `[Device]` definition, or a let, if or match
    /// whose body does. Arguments and conditions are pure -- Codex binds an
    /// effectful value only with `<-`.
    fn is_effectful(&self, e: &IrExpr) -> bool {
        use IrExpr as E;
        match e {
            E::Act(..) => true,
            E::Name(n, _, _) => self.is_device_sym(*n) || self.is_heap_mark(*n),
            E::Apply(..) => {
                let mut head = e;
                while let E::Apply(f, _, _, _) = head {
                    head = f;
                }
                matches!(head, E::Name(n, _, _) if self.is_device_sym(*n) || self.is_heap_mark(*n))
            }
            E::Let(_, _, _, body, _) => self.is_effectful(body),
            E::If(_, t, f, _, _) => self.is_effectful(t) || self.is_effectful(f),
            E::Match(_, bs, _, _) => bs.iter().any(|b| self.is_effectful(&b.body)),
            _ => false,
        }
    }

    fn is_device_sym(&self, n: Sym) -> bool {
        self.device_ops.contains(&n) || self.device_defs.contains(&n)
    }

    /// `__heap-save` or `__heap-restore` where memory is threaded (`heap_live`).
    fn is_heap_mark(&self, n: Sym) -> bool {
        self.heap_live && matches!(self.syms.text(n), "__heap-save" | "__heap-restore")
    }

    /// The threaded state is `dev`, `dev1`, ... for a GPU device, `mem`,
    /// `mem1`, ... for an address space, and `machine`, `machine1`, ... for
    /// the machine: a Codex name spelled like one would shadow it.
    fn dev_base(&self) -> &'static str {
        match self.state {
            "Mem" => "mem",
            "Machine" => "machine",
            _ => "dev",
        }
    }

    /// Whether the state was found by closure over the call graph -- an
    /// address space, or the machine when a device builtin is reached too --
    /// rather than read off a `[Device]` type.
    fn by_closure(&self) -> bool {
        self.state != "Device"
    }

    fn no_dev_name(&self, n: Sym) -> Result<(), String> {
        let id = self.local(n)?;
        let base = self.dev_base();
        if id.starts_with(base) && id[base.len()..].chars().all(|c| c.is_ascii_digit()) {
            return Err(format!("`{id}` is spelled like the threaded {}", self.state));
        }
        Ok(())
    }

    fn fresh_dev(&mut self) -> String {
        self.dev_n += 1;
        format!("{}{}", self.dev_base(), self.dev_n)
    }

    /// A hoisted call's answer. The double underscore is not a spelling any
    /// Codex identifier reaches, and the number is the DEFINITION's: a
    /// chapter's text must not depend on how many temporaries the chapters
    /// ahead of it took (`carried_value` has the rest of that story).
    fn fresh_tmp(&mut self) -> String {
        self.tmp_n += 1;
        format!("{}__{}", self.dev_base(), self.tmp_n)
    }

    fn cur_dev(&self) -> Result<String, String> {
        self.dev.clone().ok_or_else(|| format!("the {} effect outside a threaded definition", self.state))
    }

    /// Whether an expression CONTAINS an effectful call anywhere, not only
    /// in a position `is_effectful` looks at. In Mem mode that is the
    /// question, since a poke can be an argument.
    fn has_effect(&self, e: &IrExpr) -> bool {
        let mut hit = false;
        e.walk(&mut |x| {
            if let IrExpr::Name(n, _, _) = x {
                if self.is_device_sym(*n) {
                    hit = true;
                }
            }
        });
        hit
    }

    /// Emit `e` and take the bindings it hoisted, for the caller to write
    /// ahead of it.
    fn hoisting(&mut self, e: &IrExpr, ind: usize) -> Result<(Vec<String>, String), String> {
        let mark = self.hoist.len();
        let x = self.expr(e, ind)?;
        Ok((self.hoist.split_off(mark), x))
    }

    /// An expression under the Device effect, as a Roc expression whose
    /// value is `(Device.Device, T)`: the device comes in as `self.dev` and
    /// goes out in the pair. A pure expression is paired with the device
    /// unchanged; an act threads it statement by statement; let, if and a
    /// call pass it along. `self.dev` is as it was on return, since the
    /// pair is the only way a device leaves.
    fn eff_expr(&mut self, e: &IrExpr, ind: usize) -> Result<String, String> {
        use IrExpr as E;
        let dev = self.cur_dev()?;
        if !self.is_effectful(e) {
            let (lines, x) = self.hoisting(e, ind)?;
            if lines.is_empty() {
                return Ok(format!("({dev}, {x})"));
            }
            let tabs = "\t".repeat(ind + 1);
            let body: String = lines.iter().map(|l| format!("{tabs}{l}\n")).collect();
            let out = format!("({{\n{body}{tabs}({}, {x})\n{}}})", self.cur_dev()?, "\t".repeat(ind));
            self.dev = Some(dev);
            return Ok(out);
        }
        // A poke standing inside an argument or a condition hoists a
        // binding, and it belongs ahead of whatever this arm builds.
        let mark = self.hoist.len();
        let out = match e {
            E::Act(stmts, _, _) => {
                let tabs = "\t".repeat(ind + 1);
                let mut out = String::from("({\n");
                let mark = self.locals.len();
                let Some(last) = stmts.len().checked_sub(1) else {
                    return Err("an empty act".into());
                };
                for (i, st) in stmts.iter().enumerate() {
                    let rest: Vec<&IrExpr> = stmts[i + 1..].iter().map(|s| s.expr()).collect();
                    match st {
                        IrActStmt::Exec(x, _) => {
                            if i == last {
                                out.push_str(&format!("{tabs}{}\n", self.eff_expr(x, ind + 1)?));
                            } else if self.is_effectful(x) {
                                let v = self.eff_expr(x, ind + 1)?;
                                let d = self.fresh_dev();
                                out.push_str(&format!("{tabs}({d}, _) = {v}\n"));
                                self.dev = Some(d);
                            } else {
                                let (lines, x) = self.hoisting(x, ind + 1)?;
                                for l in lines {
                                    out.push_str(&format!("{tabs}{l}\n"));
                                }
                                out.push_str(&format!("{tabs}_ = {x}\n"));
                            }
                        }
                        IrActStmt::Bind(n, bty, x, _) => {
                            self.no_dev_name(*n)?;
                            if self.is_effectful(x) {
                                let v = self.eff_expr(x, ind + 1)?;
                                let d = self.fresh_dev();
                                self.locals.push(*n);
                                let b = if i == last { self.local(*n)? } else { self.binder(*n, &rest)? };
                                out.push_str(&format!("{tabs}({d}, {b}) = {v}\n"));
                                self.dev = Some(d);
                            } else {
                                let (lines, v) = self.hoisting(x, ind + 1)?;
                                for l in lines {
                                    out.push_str(&format!("{tabs}{l}\n"));
                                }
                                self.locals.push(*n);
                                let b = if i == last { self.local(*n)? } else { self.binder(*n, &rest)? };
                                out.push_str(&self.local_annotation(&b, bty, &tabs)?);
                                out.push_str(&format!("{tabs}{b} = {v}\n"));
                            }
                            if i == last {
                                out.push_str(&format!("{tabs}({}, {})\n", self.cur_dev()?, self.local(*n)?));
                            }
                        }
                    }
                }
                out.push_str(&format!("{}}})", "\t".repeat(ind)));
                self.locals.truncate(mark);
                out
            }
            E::Let(..) => self.eff_let(e, ind)?,
            E::If(c, t, f, _, _) => format!(
                "(if {} {{ {} }} else {{ {} }})",
                self.expr(c, ind)?,
                self.eff_expr(t, ind)?,
                self.eff_expr(f, ind)?
            ),
            E::Name(n, _, _) => self.eff_call(*n, &[], ind)?,
            E::Apply(..) => {
                let mut args = Vec::new();
                let mut head = e;
                while let E::Apply(f, a, _, _) = head {
                    args.push(&**a);
                    head = f;
                }
                args.reverse();
                let E::Name(n, _, _) = head else {
                    return Err("an effectful call whose head is not a name".into());
                };
                self.eff_call(*n, &args, ind)?
            }
            E::Match(..) => self.eff_match(e, ind)?,
            _ => return Err("an effectful form".into()),
        };
        let out = if self.hoist.len() > mark {
            let tabs = "\t".repeat(ind + 1);
            let lines: String = self.hoist.split_off(mark).iter().map(|l| format!("{tabs}{l}\n")).collect();
            format!("({{\n{lines}{tabs}{out}\n{}}})", "\t".repeat(ind))
        } else {
            out
        };
        self.dev = Some(dev);
        Ok(out)
    }

    // **EACH ARM ANSWERS THE STATE WITH ITS VALUE.** Only one arm
    // runs, so a write inside one cannot be lifted ahead of the
    // match; the whole match is pair-valued instead, exactly as a
    // conditional is. The scrutinee is emitted before any arm, so
    // whatever it hoists is already owed to the enclosing block.
    /// **A LOCAL OF A PLAIN TYPE IS ANNOTATED**: `s : CceText` above `s = "abc"`.
    /// Unannotated, Roc generalises the binding, and a string or number literal in
    /// it stays a `Str` or a fraction where its uses want a `CceText` or an `I64`;
    /// Roc converts at each use, and a translation to a language without that
    /// polymorphism (Rust) cannot. Text, numbers, booleans, chars and lists of
    /// them; nothing with a type variable.
    fn local_annotation(&mut self, b: &str, ty: &Ty, tabs: &str) -> Result<String, String> {
        fn plain(t: &Ty) -> bool {
            match t {
                Ty::Text | Ty::Integer(..) | Ty::Real(..) | Ty::Boolean | Ty::Char => true,
                Ty::List(e) => plain(e),
                _ => false,
            }
        }
        if b == "_" || b.starts_with('_') || !plain(strip_unit(ty)) {
            return Ok(String::new());
        }
        Ok(format!("{tabs}{b} : {}\n", self.ty(ty)?))
    }

    /// **A MATCH ON A CHAR MATCHES ITS CODE**: `match CceChar.code(c) { 15 => ...}`.
    /// A code as a pattern would need `CceChar.from_numeral`, and a nominal over a
    /// number with a literal conversion cannot tell its own values from literals
    /// to convert. So a char pattern is a code, on the scrutinee's code, and only
    /// there: `char_match` says the match being written is one.
    fn scrutinee(&mut self, sc: &IrExpr, ind: usize) -> Result<String, String> {
        let x = self.expr(sc, ind)?;
        self.char_match = matches!(strip_unit(&sc.ty()), Ty::Char);
        Ok(if self.char_match {
            self.imports.insert("CceChar".into());
            format!("CceChar.code({x})")
        } else {
            x
        })
    }

    fn eff_match(&mut self, e: &IrExpr, ind: usize) -> Result<String, String> {
        use IrExpr as E;
        let E::Match(sc, bs, _, _) = e else {
            return Err("eff_match on something else".into());
        };

            let tabs = "\t".repeat(ind + 1);
            let mut out = format!("(match {} {{\n", self.scrutinee(sc, ind)?);
            let char_match = self.char_match;
            let entry = self.cur_dev()?;
            for b in bs {
                let mark = self.locals.len();
                self.char_match = char_match;
                let pat = self.pattern(&b.pattern, &[&b.body, &b.guard])?;
                let guard = match &b.guard {
                    E::BoolLit(true, _) => String::new(),
                    g => format!(" if {}", self.expr(g, ind + 1)?),
                };
                if self.has_effect(&b.guard) {
                    return Err("a match guard that touches memory".into());
                }
                self.dev = Some(entry.clone());
                let body = self.eff_expr(&b.body, ind + 1)?;
                self.locals.truncate(mark);
                out.push_str(&format!("{tabs}{pat}{guard} => {body}\n"));
            }
        self.dev = Some(entry);
        out.push_str(&format!("{}}})", "\t".repeat(ind)));
        Ok(out)
    }

    /// A let chain under the threaded state, as a pair-valued block. Both
    /// the effectful path and a poke standing inside an ordinary
    /// expression come here, so it is a method rather than an arm.
    fn eff_let(&mut self, e: &IrExpr, ind: usize) -> Result<String, String> {
        use IrExpr as E;
            let tabs = "\t".repeat(ind + 1);
            let mut out = String::from("({\n");
            let mark = self.locals.len();
            let mut cur = e;
            while let E::Let(n, lty, v, body, _) = cur {
                self.no_dev_name(*n)?;
                // **A WRITE IS OFTEN A LET NOBODY READS.** `let w =
                // poke-byte addr 0 v in peek-byte addr 0` is how every
                // fill loop in the corpus is written, so a let whose
                // value touches the state binds the state too.
                if self.is_effectful(v) {
                    let v = self.eff_expr(v, ind + 1)?;
                    let dn = self.fresh_dev();
                    self.locals.push(*n);
                    let b = self.binder(*n, &[body])?;
                    out.push_str(&format!("{tabs}({dn}, {b}) = {v}\n"));
                    self.dev = Some(dn);
                    cur = body;
                    continue;
                }
                let (lines, v) = self.hoisting(v, ind + 1)?;
                for l in lines {
                    out.push_str(&format!("{tabs}{l}\n"));
                }
                self.locals.push(*n);
                let b = self.binder(*n, &[body])?;
                out.push_str(&self.local_annotation(&b, lty, &tabs)?);
                out.push_str(&format!("{tabs}{b} = {v}\n"));
                cur = body;
            }
            out.push_str(&format!("{tabs}{}\n{}}})", self.eff_expr(cur, ind + 1)?, "\t".repeat(ind)));
        self.locals.truncate(mark);
        Ok(out)
    }

    /// A call under the Device effect: a `[Device]` definition with the
    /// device first, or one of the effect's operations on the Device module.
    fn eff_call(&mut self, n: Sym, args: &[&IrExpr], ind: usize) -> Result<String, String> {
        // **THE ARGUMENTS RUN FIRST.** In Mem mode one of them may poke,
        // and the state this call is handed has to be the one those writes
        // left behind, so it is read after they are emitted, not before.
        let mut xs = Vec::new();
        for a in args {
            if self.is_effectful(a) && !self.by_closure() {
                return Err("an effectful argument".into());
            }
            xs.push(self.expr(a, ind)?);
        }
        xs.insert(0, self.cur_dev()?);
        let text = self.syms.text(n).to_string();
        if self.device_defs.contains(&n) {
            let k = self.arity[&n];
            if args.len() != k {
                // **A FUNCTION VALUE CARRIES NO STATE.** Short of its arguments,
                // the call is a closure, and a closure is handed on and entered
                // where nothing threads the device, memory or machine it reaches.
                let what = match self.state {
                    "Machine" => "the machine",
                    "Mem" => "memory",
                    _ => "the device",
                };
                return Err(format!(
                    "a function value from `{text}` ({} of {k} arguments), which reaches {what}; a function value carries no state",
                    args.len()
                ));
            }
            return Ok(format!("{}({})", self.def_ref(n)?, xs.join(", ")));
        }
        let want = |k: usize| -> Result<(), String> {
            if args.len() == k {
                Ok(())
            } else {
                Err(format!("`{text}` applied to {} arguments, takes {k}", args.len()))
            }
        };
        self.imports.insert(self.state.into());
        if self.by_closure() {
            let s = self.state;
            // A memory door that reads or writes is an effect, under the machine
            // as under `Mem`: a platform may keep the bytes, and the GPU they
            // feed (see `MEM`, and roc-apps framebuffer/roc/Machine.roc).
            let mem_bang = "!";
            // A heap mark is the bump pointer, as x86's r10 is: `__heap-save`
            // answers it and `__heap-restore` rewinds to it, answering 0.
            if text == "__heap-save" {
                want(0)?;
                return Ok(format!("{s}.mark({})", xs[0]));
            }
            if text == "__heap-restore" {
                want(1)?;
                return Ok(format!("{s}.release({}, {})", xs[0], xs[1]));
            }
            // A device builtin is the machine's door of the same name, and the
            // door answers as x86 does: `port-out-32`, a block write and a
            // select answer 0, and a block read answers the address of the
            // sector it bump-allocated. Only the machine threads one. A block
            // door is an effect, spelled with `!`: the disk may be the host's
            // (roc-apps machine/native). So is every port door: the byte and
            // 16-bit ones reach the IDE channel and through it the disk, and
            // the 32-bit ones the GPU a platform may keep (roc-apps framebuffer).
            // So are the UEFI key reads, which take the key cell out of memory a
            // platform may keep.
            // `gpu-out` and `gpu-in` are port-out-32 and port-in-32 under the
            // Gpu.Compute row, as x86 emits them; the port decides the rest.
            let name = match text.as_str() {
                "gpu-out" => "port-out-32",
                "gpu-in" => "port-in-32",
                t => t,
            };
            let door = match name {
                "port-in-16-block" | "port-out-16-block" => Some(3),
                "net-send-raw" => Some(2),
                "net-recv-raw" | "net-get-hwaddr" => Some(1),
                "net-status" => Some(0),
                "port-out-32" | "port-out-byte" | "port-out-16" | "block-write-sector" | "process-restrict-cap"
                | "process-set-scope" => Some(2),
                "port-in-32" | "port-in-byte" | "port-in-16" | "block-read-sector" | "block-select" | "process-get-scope"
                | "process-get-cap" | "process-get-network-scope" => Some(1),
                "block-sector-count" | "process-get-pid" | "process-yield" | "uefi-read-key-ex" | "uefi-read-key" => Some(0),
                _ => None,
            };
            if let Some(k) = door {
                want(k)?;
                let bang = if text.starts_with("block-")
                    || name.starts_with("port-")
                    || text.starts_with("uefi-read-key")
                    || text == "net-send-raw"
                    || text == "net-recv-raw"
                {
                    "!"
                } else {
                    ""
                };
                // A scope is text, and the machine keeps one as a Str: units
                // leave through `printed` and come back through `of_str`.
                let mut xs = xs.to_vec();
                if name == "process-set-scope" {
                    self.uses_text = true;
                    self.imports.insert("CceText".into());
                    let last = xs.len() - 1;
                    xs[last] = format!("CceText.printed({})", xs[last]);
                }
                let call = format!("{s}.{}{bang}({})", name.replace('-', "_"), xs.join(", "));
                if name == "process-get-scope" || name == "process-get-network-scope" {
                    self.uses_text = true;
                    self.imports.insert("CceText".into());
                    return Ok(format!("CceText.answer_units({call})"));
                }
                return Ok(call);
            }
            // base, offset [, value]; a load answers the value and a store
            // answers 0, as the interpreter does.
            let width = |b: &str| -> Option<&'static str> {
                match b {
                    "peek-byte" | "poke-byte" | "read-mmio" | "poke-mmio" => Some("1"),
                    "peek-16" | "poke-16" => Some("2"),
                    "peek-32" | "poke-32" | "read-mmio-32" | "poke-mmio-32" | "gpu-mem-read" | "gpu-mem-write" => Some("4"),
                    "peek-qword" | "poke-qword" => Some("8"),
                    _ => None,
                }
            };
            if let Some(w) = width(&text) {
                let load = text.starts_with("peek") || text.starts_with("read") || text == "gpu-mem-read";
                let want = if load { 2 } else { 3 };
                if args.len() != want {
                    return Err(format!("`{text}` applied to {} arguments, takes {want}", args.len()));
                }
                // The byte-width MMIO pair is the one memory builtin x86 does
                // not check against the GPU's page.
                let f = match (load, text.as_str()) {
                    (true, "read-mmio") => "load_unguarded",
                    (false, "poke-mmio") => "store_unguarded",
                    (true, _) => "load",
                    (false, _) => "store",
                };
                return Ok(format!("{s}.{f}{mem_bang}({}, {w})", xs.join(", ")));
            }
            if text == "alloc-bytes" {
                if args.len() != 1 {
                    return Err("`alloc-bytes` takes one argument".into());
                }
                return Ok(format!("{s}.alloc({})", xs.join(", ")));
            }
            // `__heap-advance n` moves the bump pointer past `n` bytes and
            // answers Nothing: `alloc-bytes` without the address.
            if text == "__heap-advance" {
                want(1)?;
                return Ok(format!("{s}.advance({})", xs.join(", ")));
            }
            if text == "__buf-write-byte" {
                want(3)?;
                return Ok(format!("{s}.write_byte{mem_bang}({})", xs.join(", ")));
            }
            if text == "__buf-write-bytes" {
                want(3)?;
                return Ok(format!("{s}.write_bytes{mem_bang}({})", xs.join(", ")));
            }
            if text == "__buf-read-bytes" {
                want(3)?;
                return Ok(format!("{s}.read_bytes{mem_bang}({})", xs.join(", ")));
            }
            // `atomic-exchange addr v` swaps the qword at the address for `v`
            // and answers the old one, x86's xchg.
            if text == "atomic-exchange" {
                want(2)?;
                return Ok(format!("{s}.exchange{mem_bang}({}, {}, {})", xs[0], xs[1], xs[2]));
            }
            // `atomic-load addr` and `atomic-store addr v` are a qword at the
            // address, x86's mov and xchg; the store answers 0.
            if text == "atomic-load" || text == "atomic-store" {
                let load = text == "atomic-load";
                let want = if load { 1 } else { 2 };
                if args.len() != want {
                    return Err(format!("`{text}` applied to {} arguments, takes {want}", args.len()));
                }
                // The state leads `xs`, as it does for every door. x86's atomic
                // helpers do not check the GPU's page, so on the machine they
                // take the unguarded doors.
                let (l, st) = if s == "Machine" { ("load_unguarded", "store_unguarded") } else { ("load", "store") };
                return Ok(if load {
                    format!("{s}.{l}{mem_bang}({}, {}, 0, 8)", xs[0], xs[1])
                } else {
                    format!("{s}.{st}{mem_bang}({}, {}, 0, {}, 8)", xs[0], xs[1], xs[2])
                });
            }
        }
        Ok(match text.as_str() {
            "device-load" => {
                want(2)?;
                format!("Device.load({})", xs.join(", "))
            }
            "device-store" => {
                want(3)?;
                format!("Device.store({})", xs.join(", "))
            }
            "thread-idx-x" => {
                want(0)?;
                format!("Device.thread_idx_x({})", xs[0])
            }
            "block-idx-x" => {
                want(0)?;
                format!("Device.block_idx_x({})", xs[0])
            }
            "block-dim-x" => {
                want(0)?;
                format!("Device.block_dim_x({})", xs[0])
            }
            other => return Err(format!("Device operation `{other}`")),
        })
    }

    /// A binder that nothing reads is spelled `_name`, which is Roc's way of
    /// saying so; an unused variable is a warning, and a warning is exit 2.
    /// A heap mark handed only to `__heap-restore` is read by nothing, since
    /// the restore is emitted as `0`.
    fn binder(&self, n: Sym, scope: &[&IrExpr]) -> Result<String, String> {
        let restore = if self.heap_live { None } else { self.syms.find("__heap-restore") };
        let used = scope.iter().any(|e| reads(e, n, restore));
        let id = self.local(n)?;
        Ok(if used { id } else { format!("_{id}") })
    }

    // ---- expressions ----------------------------------------------------

    fn expr(&mut self, e: &IrExpr, ind: usize) -> Result<String, String> {
        use IrExpr as E;
        if let Some(fold) = self.fold.take() {
            let out = self.fold_expr(e, ind, &fold);
            self.fold = Some(fold);
            return out;
        }
        Ok(match e {
            E::IntLit(v, _) => int_lit(*v),
            E::NumLit(bits, _) => num_lit(*bits, self.wgsl),
            E::TextLit(s, _) => {
                self.imports.insert("CceText".into());
                crate::roc_text::literal(s)
            }
            E::BoolLit(b, _) => if *b { "True".into() } else { "False".into() },
            // The IR carries a char literal as its CODE already.
            E::CharLit(c, _) => {
                self.imports.insert("CceChar".into());
                format!("CceChar.of_code({})", int_lit(*c))
            }
            E::Name(n, _, _) => self.name_value(*n)?,
            // **A SHORT-CIRCUIT OPERAND IS NOT ALWAYS EVALUATED**, so a
            // poke in one cannot be hoisted ahead of the operator. Write
            // out the conditional the operator means -- `a and b` is `if a
            // then b else False` -- and thread the state through it.
            E::Binary(op, l, r, _, _)
                if self.by_closure()
                    && self.dev.is_some()
                    && matches!(op, IrBinOp::And | IrBinOp::Or)
                    && self.has_effect(r) =>
            {
                let l = self.expr(l, ind)?;
                let entry = self.cur_dev()?;
                let rr = self.eff_expr(r, ind)?;
                self.dev = Some(entry.clone());
                let (yes, no) = match op {
                    IrBinOp::And => (rr, format!("({entry}, False)")),
                    _ => (format!("({entry}, True)"), rr),
                };
                let d = self.fresh_dev();
                let tmp = self.fresh_tmp();
                self.hoist.push(format!("({d}, {tmp}) = (if {l} {{ {yes} }} else {{ {no} }})"));
                self.dev = Some(d);
                tmp
            }
            E::Binary(op, l, r, t, _) => {
                // `~` counts units of its OPERANDS' width; the mode
                // operations take the width from the result.
                let f32 = matches!(l.ty(), Ty::Real(RealWidth::F32, _)) || matches!(t, Ty::Real(RealWidth::F32, _));
                let (l, r) = (self.expr(l, ind)?, self.expr(r, ind)?);
                // **THE OVERFLOW MODE IS ON THE TYPE.** A field declared
                // `Integer between lo and hi wrapping` (Rng's LCG state) wraps
                // where Roc's `+` would crash; the checker carries the mode on
                // every node of that type, so the spelling follows the node.
                let wrap = matches!(t, Ty::Integer(_, _, crate::check::Overflow::Wrapping));
                if matches!(t, Ty::Integer(_, _, crate::check::Overflow::Clamping)) {
                    return Err("a clamping integer".into());
                }
                self.binary(*op, l, r, wrap, f32)?
            }
            // **A NEGATED LITERAL IS ONE LITERAL.** The lowest integer is
            // written `-9223372036854775808`, which is a negate over a
            // literal that does not fit, so the IR carries it already
            // wrapped and negating again overflows (codex/test's
            // ops/int-wrapping-spelling).
            E::Negate(x, _, _) if matches!(&**x, E::IntLit(..)) => {
                let E::IntLit(v, _) = &**x else { unreachable!() };
                int_lit(v.wrapping_neg())
            }
            E::Negate(x, t, _) => {
                let x = self.expr(x, ind)?;
                // Negating the lowest integer overflows, and a wrapping
                // type says to wrap rather than crash: codex/test's
                // ops/int-wrapping-spelling negates I64.lowest on purpose.
                let wrap = self.wgsl || matches!(t, Ty::Integer(_, _, crate::check::Overflow::Wrapping));
                if wrap && matches!(t, Ty::Integer(..)) {
                    format!("{}.minus_wrap(0, {x})", self.int())
                } else {
                    format!("(-{x})")
                }
            }
            // **A CONDITIONAL THAT POKES CANNOT BE HOISTED OUT OF**: only
            // one branch runs, so the write stays inside it and the whole
            // if answers the state alongside its value, as a `[Device]`
            // definition does.
            E::If(c, t, f, _, _)
                if self.by_closure()
                    && self.dev.is_some()
                    && (self.has_effect(t) || self.has_effect(f)) =>
            {
                let c = self.expr(c, ind)?;
                let entry = self.cur_dev()?;
                let tt = self.eff_expr(t, ind)?;
                self.dev = Some(entry.clone());
                let ff = self.eff_expr(f, ind)?;
                self.dev = Some(entry);
                let d = self.fresh_dev();
                let tmp = self.fresh_tmp();
                self.hoist.push(format!("({d}, {tmp}) = (if {c} {{ {tt} }} else {{ {ff} }})"));
                self.dev = Some(d);
                tmp
            }
            E::If(c, t, f, _, _) => format!(
                "(if {} {{ {} }} else {{ {} }})",
                self.expr(c, ind)?,
                self.expr(t, ind)?,
                self.expr(f, ind)?
            ),
            E::Match(_, bs, _, _)
                if self.by_closure()
                    && self.dev.is_some()
                    && bs.iter().any(|b| self.has_effect(&b.body)) =>
            {
                let block = self.eff_match(e, ind)?;
                let d = self.fresh_dev();
                let tmp = self.fresh_tmp();
                self.hoist.push(format!("({d}, {tmp}) = {block}"));
                self.dev = Some(d);
                tmp
            }
            // **A BLOCK KEEPS ITS OWN BINDINGS**, so a poke inside one
            // cannot be lifted past it; the block answers the state
            // alongside its value instead, and the binding of the pair is
            // what the enclosing expression hoists. Without this the
            // writes happen and the memory that holds them is dropped.
            E::Let(..) if self.by_closure() && self.dev.is_some() && self.has_effect(e) => {
                let block = self.eff_let(e, ind)?;
                let d = self.fresh_dev();
                let tmp = self.fresh_tmp();
                self.hoist.push(format!("({d}, {tmp}) = {block}"));
                self.dev = Some(d);
                tmp
            }
            E::Let(..) => match carried_value(e) {
                IrExpr::Let(..) => self.let_block(e, ind)?,
                inner => self.expr(inner, ind)?,
            },
            E::Apply(..) => self.apply(e, ind)?,
            E::Lambda(..) => return Err("lambda".into()),
            E::List(xs, _, _) => {
                let mut items = Vec::new();
                for x in xs {
                    items.push(self.expr(x, ind)?);
                }
                format!("[{}]", items.join(", "))
            }
            E::Match(sc, bs, _, _) => {
                let tabs = "\t".repeat(ind + 1);
                let mut out = format!("(match {} {{\n", self.scrutinee(sc, ind)?);
                let char_match = self.char_match;
                for b in bs {
                    let mark = self.locals.len();
                    self.char_match = char_match;
                    let pat = self.pattern(&b.pattern, &[&b.body, &b.guard])?;
                    let guard = match &b.guard {
                        E::BoolLit(true, _) => String::new(),
                        g => format!(" if {}", self.expr(g, ind + 1)?),
                    };
                    let body = self.expr(&b.body, ind + 1)?;
                    self.locals.truncate(mark);
                    out.push_str(&format!("{tabs}{pat}{guard} => {body}\n"));
                }
                out.push_str(&format!("{}}})", "\t".repeat(ind)));
                out
            }
            // **AN ACT IS A BLOCK.** Under the Device effect an act threads
            // the device (`eff_expr`); under Console it does not thread
            // anything, so the statements are the block's and the last one
            // is its value, which is what Codex says an act answers.
            E::Act(stmts, _, _) => self.act_block(stmts, ind)?,
            // **A CLAMPING FIELD CLAMPS WHERE IT IS BUILT.** `p : Integer
            // between 0 and 100 clamping` holds 100 when handed 150, and the
            // clamp is the record's, not the arithmetic's: the IR types the
            // value as it was written (codex/test's arithmetic, which read
            // 150 before this).
            E::Record(n, fs, _, _) => {
                if fs.is_empty() {
                    return Ok("{}".into());
                }
                let mut items = Vec::new();
                for f in fs {
                    let v = self.expr(&f.value, ind)?;
                    let v = match self.tds.field(*n, f.name) {
                        Some(Ty::Integer(lo, hi, crate::check::Overflow::Clamping)) => {
                            let (lo, hi) = (*lo, *hi);
                            format!("{int}.min({int}.max({v}, {lo}), {hi})", int = self.int())
                        }
                        // A wrapping field wraps into its range where it is
                        // built, `lo + (v - lo) rem_euclid span` as the
                        // interpreter's `apply_bound`; `mod_by` is floored,
                        // which is Euclidean for a positive span.
                        Some(Ty::Integer(lo, hi, crate::check::Overflow::Wrapping))
                            if (*hi as i128 - *lo as i128 + 1) <= i64::MAX as i128 =>
                        {
                            let (lo, span) = (*lo, *hi - *lo + 1);
                            format!("({lo} + {int}.mod_by({v} - ({lo}), {span}))", int = self.int())
                        }
                        _ => v,
                    };
                    items.push(format!("{}: {}", self.ident(f.name)?, v));
                }
                if self.nominal.contains(n) {
                    format!("{}.{{ {} }}", self.type_ref(*n), items.join(", "))
                } else {
                    format!("{{ {} }}", items.join(", "))
                }
            }
            E::FieldAccess(r, slot, _, _) => {
                let field = slot.split('/').next().unwrap_or(slot);
                format!("{}.{}", self.expr(r, ind)?, ident_text(field)?)
            }
            E::FieldStore(..) => return Err("field-store".into()),
            E::Handle(..) => return Err("handle".into()),
            E::WithTimeout(..) => return Err("with-timeout".into()),
            E::Try(..) => return Err("try".into()),
        })
    }

    /// A name standing alone: a definition (a constant, or a function as a
    /// value), a local, or a nullary constructor. A builtin as a VALUE has no
    /// Roc spelling here.
    fn name_value(&mut self, n: Sym) -> Result<String, String> {
        let n = self.instance_base(n);

        if self.locals.contains(&n) {
            return self.local(n);
        }
        if self.is_device_sym(n) {
            if self.by_closure() && self.dev.is_some() {
                let call = self.eff_call(n, &[], 0)?;
                let d = self.fresh_dev();
                let t = self.fresh_tmp();
                self.hoist.push(format!("({d}, {t}) = {call}"));
                self.dev = Some(d);
                return Ok(t);
            }
            return Err(format!("`{}` performs the Device effect outside a statement", self.syms.text(n)));
        }
        if let Some(&k) = self.arity.get(&n) {
            let f = self.def_ref(n)?;
            // A definition that answers a function takes its own `k`
            // parameters, then the answer's; as a value it takes them all at
            // once, as every Roc function value does (`partial`).
            let takes = self.defs.iter().find(|d| d.name == n).map_or(0, |d| arrows_of(&d.ty));
            if k > 0 && takes > k {
                return Ok(self.partial(&f, Vec::new(), k, takes, 0));
            }
            return Ok(f);
        }
        let t = self.syms.text(n);
        if t.starts_with(|c: char| c.is_ascii_uppercase()) {
            return self.tag(n);
        }
        // A bump-allocator checkpoint (Chess takes one around every search
        // step). Roc's memory is counted, so the mark is nothing.
        if t == "__heap-save" {
            return Ok("0".into());
        }
        // A builtin x86 emits as a constant (`pit-input-hz`, `pit-count`) is
        // that constant, read from upstream by the builtins probe. `cpu-park`
        // is `sti; hlt` and answers 0: a hosted program has no core to park.
        if let Some(v) = crate::builtins::constant_builtin(t) {
            return Ok(int_lit(v));
        }
        if t == "cpu-park" {
            return Ok("0".into());
        }
        // `__heap-base` is where the target's heap begins (upstream answers it
        // per backend: x86's `bare-metal-heap-base`, wasm's `$heap_start`).
        // Both of rocemit's memories, `Mem` and `MachineMem`, open their bump
        // pointer there, at 6291456; the `+ z` in `new` is only there to keep
        // the heap out of the compiler's reach.
        if t == "__heap-base" {
            return Ok("6291456".into());
        }
        Err(format!("builtin `{t}` used as a value"))
    }

    /// **AN INSTANCE NAME IS ITS BASE.** `==` on a constructed type with
    /// arguments is lowered as upstream's x86 emitter spells it, a call of
    /// `__eq_<T>@<keys>`, one name per instance of the element types; the
    /// derived definition is `__eq_<T>` alone, and in Roc it is one function,
    /// its `where` clause dispatching the elements' equality. So a name with
    /// an `@` is looked up without it.
    fn instance_base(&self, n: Sym) -> Sym {
        let t = self.syms.text(n);
        match t.find('@') {
            Some(i) => self.syms.find(&t[..i]).unwrap_or(n),
            None => n,
        }
    }

    /// An act as a Roc block: `x <- e` binds, a bare statement runs, and
    /// the last statement is the value.
    fn act_block(&mut self, stmts: &[IrActStmt], ind: usize) -> Result<String, String> {
        let Some(last) = stmts.len().checked_sub(1) else {
            return Err("an empty act".into());
        };
        let tabs = "\t".repeat(ind + 1);
        let mut out = String::from("({\n");
        let mark = self.locals.len();
        for (i, st) in stmts.iter().enumerate() {
            let rest: Vec<&IrExpr> = stmts[i + 1..].iter().map(|s| s.expr()).collect();
            match st {
                IrActStmt::Exec(e, _) => {
                    let e = self.expr(e, ind + 1)?;
                    out.push_str(&format!("{tabs}{e}\n"));
                }
                IrActStmt::Bind(n, _, e, _) => {
                    let e = self.expr(e, ind + 1)?;
                    self.locals.push(*n);
                    let b = if i == last { self.local(*n)? } else { self.binder(*n, &rest)? };
                    out.push_str(&format!("{tabs}{b} = {e}\n"));
                    if i == last {
                        out.push_str(&format!("{tabs}{}\n", self.local(*n)?));
                    }
                }
            }
        }
        out.push_str(&format!("{}}})", "\t".repeat(ind)));
        self.locals.truncate(mark);
        Ok(out)
    }

    /// A `let` chain is one block: `({ a = .. \n b = .. \n body })`. The parens
    /// keep it an expression -- a bare `{` opens a record.
    fn let_block(&mut self, e: &IrExpr, ind: usize) -> Result<String, String> {
        let tabs = "\t".repeat(ind + 1);
        let mut out = String::from("({\n");
        let mark = self.locals.len();
        let mut cur = carried_value(e);
        while let IrExpr::Let(n, lty, v, body, _) = cur {
            let (lines, v) = self.hoisting(v, ind + 1)?;
            for l in lines {
                out.push_str(&format!("{tabs}{l}\n"));
            }
            self.locals.push(*n);
            let b = self.binder(*n, &[body])?;
            out.push_str(&self.local_annotation(&b, lty, &tabs)?);
            out.push_str(&format!("{tabs}{b} = {v}\n"));
            cur = carried_value(body);
        }
        let (lines, tail) = self.hoisting(cur, ind + 1)?;
        for l in lines {
            out.push_str(&format!("{tabs}{l}\n"));
        }
        out.push_str(&format!("{tabs}{tail}\n{}}})", "\t".repeat(ind)));
        self.locals.truncate(mark);
        Ok(out)
    }

    fn binary(&mut self, op: IrBinOp, l: String, r: String, wrap: bool, f32: bool) -> Result<String, String> {
        use IrBinOp as B;
        let int = self.int();
        if wrap && !self.wgsl {
            match op {
                B::AddInt => return Ok(format!("{int}.plus_wrap({l}, {r})")),
                B::SubInt => return Ok(format!("{int}.minus_wrap({l}, {r})")),
                B::MulInt => return Ok(format!("{int}.times_wrap({l}, {r})")),
                _ => {}
            }
        }
        if self.wgsl {
            match op {
                B::AddInt => return Ok(format!("{int}.plus_wrap({l}, {r})")),
                B::SubInt => return Ok(format!("{int}.minus_wrap({l}, {r})")),
                B::MulInt => return Ok(format!("{int}.times_wrap({l}, {r})")),
                B::DivInt => {
                    self.imports.insert("Device".into());
                    return Ok(format!("Device.div({l}, {r})"));
                }
                B::RemInt => {
                    self.imports.insert("Device".into());
                    return Ok(format!("Device.rem({l}, {r})"));
                }
                _ => {}
            }
        }
        // A trapping or saturating Real checks each result: the helpers
        // (Prelude `trap_f64`, `sat_f32`, ...) trap on, or clamp, an infinity
        // or a NaN, as upstream's emitters test the exponent.
        let w = if f32 { "f32" } else { "f64" };
        let mut checked = |helper: &str, e: String| {
            self.imports.insert("Prelude".into());
            format!("Prelude.{helper}_{w}({e})")
        };
        match op {
            B::AddRealTrapping => return Ok(checked("trap", format!("({l} + {r})"))),
            B::SubRealTrapping => return Ok(checked("trap", format!("({l} - {r})"))),
            B::MulRealTrapping => return Ok(checked("trap", format!("({l} * {r})"))),
            B::DivRealTrapping => return Ok(checked("trap", format!("({l} / {r})"))),
            B::AddRealSaturating => return Ok(checked("sat", format!("({l} + {r})"))),
            B::SubRealSaturating => return Ok(checked("sat", format!("({l} - {r})"))),
            B::MulRealSaturating => return Ok(checked("sat", format!("({l} * {r})"))),
            B::DivRealSaturating => return Ok(checked("sat", format!("({l} / {r})"))),
            _ => {}
        }
        Ok(match op {
            B::AddInt | B::AddNum | B::AddRealApprox => format!("({l} + {r})"),
            B::SubInt | B::SubNum | B::SubRealApprox => format!("({l} - {r})"),
            B::MulInt | B::MulNum | B::MulRealApprox => format!("({l} * {r})"),
            B::DivNum | B::DivRealApprox => format!("({l} / {r})"),
            B::DivInt => format!("{int}.div_trunc_by({l}, {r})"),
            B::RemInt => format!("{int}.rem_by({l}, {r})"),
            B::PowInt => {
                self.imports.insert("Prelude".into());
                format!("Prelude.int_pow({l}, {r})")
            }
            B::Eq => format!("({l} == {r})"),
            B::NotEq => format!("({l} != {r})"),
            B::Lt => format!("({l} < {r})"),
            B::Gt => format!("({l} > {r})"),
            B::LtEq => format!("({l} <= {r})"),
            B::GtEq => format!("({l} >= {r})"),
            B::And => format!("({l} and {r})"),
            B::Or => format!("({l} or {r})"),
            B::AppendText => {
                self.imports.insert("CceText".into());
                format!("CceText.concat({l}, {r})")
            }
            B::AppendList => format!("List.concat({l}, {r})"),
            // `=~=` is ordinal equality on doubles; two doubles with the same
            // bits have the same ordinal, and -0.0 differs from 0.0 in both.
            // `~0` is ORDINAL equality, and -0.0 and +0.0 share ordinal 0
            // (codex/test's ops/real-approx-equality: `-0 ~0 +0` is True).
            B::ApproxEqExact if f32 && !self.wgsl => {
                self.imports.insert("Prelude".into());
                format!("(Prelude.ordinal32({l}) == Prelude.ordinal32({r}))")
            }
            B::ApproxEqExact if !self.wgsl => {
                self.imports.insert("Prelude".into());
                format!("(Prelude.ordinal({l}) == Prelude.ordinal({r}))")
            }
            B::ApproxEqExact => format!("({real}.to_bits({l}) == {real}.to_bits({r}))", real = self.real()),
            B::ApproxEq if f32 && !self.wgsl => {
                self.imports.insert("Prelude".into());
                format!("Prelude.approx_eq32({l}, {r})")
            }
            B::ApproxEq if !self.wgsl => {
                self.imports.insert("Prelude".into());
                format!("Prelude.approx_eq({l}, {r})")
            }
            other => return Err(format!("binary {}", other.atom())),
        })
    }

    fn apply(&mut self, e: &IrExpr, ind: usize) -> Result<String, String> {
        let mut args = Vec::new();
        let mut head = e;
        while let IrExpr::Apply(f, a, _, _) = head {
            args.push(&**a);
            head = f;
        }
        args.reverse();
        let IrExpr::Name(n, head_ty, _) = head else {
            // **A CALL ON A VALUE.** A closure kept in a record field, or any
            // other expression that answers a function, is entered with
            // every flattened parameter at once, as a local is.
            let f = format!("({})", self.expr(head, ind)?);
            let mut xs = Vec::new();
            for a in &args {
                xs.push(self.expr(a, ind)?);
            }
            let takes = arrows_of(&head.ty());
            if xs.len() < takes {
                let missing = takes - xs.len();
                return Ok(self.partial(&f, xs, missing, missing, ind));
            }
            return Ok(format!("{f}({})", xs.join(", ")));
        };
        let n = &self.instance_base(*n);
        let text = self.syms.text(*n).to_string();
        if self.is_device_sym(*n) {
            if self.by_closure() && self.dev.is_some() {
                // The arguments emit first, so whatever they hoist is
                // already in the buffer ahead of this line.
                let call = self.eff_call(*n, &args, ind)?;
                let d = self.fresh_dev();
                let t = self.fresh_tmp();
                self.hoist.push(format!("({d}, {t}) = {call}"));
                self.dev = Some(d);
                return Ok(t);
            }
            return Err(format!("`{text}` performs the Device effect outside a statement"));
        }
        let mut xs = Vec::new();
        for a in &args {
            xs.push(self.expr(a, ind)?);
        }
        if self.locals.contains(n) {
            let takes = arrows_of(head_ty);
            if xs.len() < takes {
                let missing = takes - xs.len();
                let f = self.local(*n)?;
                return Ok(self.partial(&f, xs, missing, missing, ind));
            }
            return Ok(format!("{}({})", self.local(*n)?, xs.join(", ")));
        }
        if let Some(&k) = self.arity.get(n) {
            if let Some(t) = self.unwritable_eq(*n) {
                return Err(format!("`==` on `{}`, which holds a function", self.syms.text(t)));
            }
            // **AN EFFECTFUL FUNCTION HANDED TO A PURE PARAMETER.** Codex's
            // `list-map` carries its argument's effect; the emitted one
            // takes a pure function, and Roc has no effect variable to
            // write in its place. Only this shape is a type error, so only
            // this shape is refused (codex/test's effect-map-effctx).
            if let Some(callee) = self.defs.iter().find(|d| d.name == *n) {
                let mut cur = &callee.ty;
                for a in args.iter().take(k) {
                    while let Ty::ForAll(_, b) | Ty::ForAllEff(_, b) = cur {
                        cur = b;
                    }
                    let Ty::Fun(p, _, r) = cur else { break };
                    if matches!(&**p, Ty::Fun(_, row, _) if row.labels.is_empty()) {
                        if let IrExpr::Name(an, at, _) = a {
                            let effectful = matches!(at, Ty::Fun(_, row, _) if !row.labels.is_empty())
                                || self
                                    .defs
                                    .iter()
                                    .any(|d| d.name == *an && matches!(&d.ty, Ty::Fun(_, row, _) if !row.labels.is_empty()));
                            if effectful {
                                return Err(format!(
                                    "`{}`, an effectful function, handed to `{text}`, which takes a pure one",
                                    self.syms.text(*an)
                                ));
                            }
                        }
                    }
                    cur = r;
                }
            }
            if xs.len() < k {
                let own = k - xs.len();
                let f = self.def_ref(*n)?;
                return Ok(self.partial(&f, xs, own, own.max(arrows_of(&e.ty())), ind));
            }
            let first = format!("{}({})", self.def_ref(*n)?, xs[..k].join(", "));
            return Ok(if xs.len() == k { first } else { format!("{first}({})", xs[k..].join(", ")) });
        }
        if text.starts_with(|c: char| c.is_ascii_uppercase()) {
            return Ok(format!("{}({})", self.tag(*n)?, xs.join(", ")));
        }
        self.builtin(&text, &args, xs)
    }

    /// **A PARTIAL APPLICATION IS A CLOSURE OVER THE REST.** A function value
    /// is uncurried in Roc (`fun_parts`), so the closure takes every
    /// parameter its type flattens to: `own` of them go to `f`, and the rest
    /// to what `f` answers. Each argument is bound once, outside the closure,
    /// so it is evaluated where the application is and not at every call.
    fn partial(&mut self, f: &str, xs: Vec<String>, own: usize, rest: usize, ind: usize) -> String {
        let tabs = "\t".repeat(ind + 1);
        let mut out = String::from("({\n");
        let mut given = Vec::new();
        for x in xs {
            let t = self.fresh_tmp();
            out.push_str(&format!("{tabs}{t} = {x}\n"));
            given.push(t);
        }
        let ps: Vec<String> = (0..rest).map(|_| self.fresh_tmp()).collect();
        let mut call = format!("{f}({})", given.iter().chain(&ps[..own]).cloned().collect::<Vec<_>>().join(", "));
        if rest > own {
            call = format!("{call}({})", ps[own..].join(", "));
        }
        out.push_str(&format!("{tabs}|{}| {call}\n{}}})", ps.join(", "), "\t".repeat(ind)));
        out
    }

    fn builtin(&mut self, name: &str, args: &[&IrExpr], xs: Vec<String>) -> Result<String, String> {
        let want = |k: usize| -> Result<(), String> {
            if xs.len() == k {
                Ok(())
            } else {
                Err(format!("`{name}` applied to {} arguments, takes {k}", xs.len()))
            }
        };
        // `list_versions`' copy-out tuple and its elements.
        if name == crate::list_versions::TUPLE {
            return Ok(format!("({})", xs.join(", ")));
        }
        if let Some(k) = name.strip_prefix(crate::list_versions::AT) {
            want(1)?;
            return Ok(format!("{}.{k}", xs[0]));
        }
        let (int, real, uint) = (self.int(), self.real(), self.uint());
        let int_lc = int.to_ascii_lowercase();
        Ok(match name {
            "list-length" => {
                want(1)?;
                format!("U64.to_{int_lc}_wrap(List.len({}))", xs[0])
            }
            "list-at" => {
                want(2)?;
                format!("(List.get({}, {int}.to_u64_wrap({})) ?? crash(\"list-at out of range\"))", xs[0], xs[1])
            }
            // **CODEX MUTATES IN PLACE; ROC ANSWERS A NEW LIST.**
            // `list_versions` has already made every later read of the list,
            // here and in the callers, read this answer. Past the end is a
            // crash in both.
            "list-set-at" => {
                want(3)?;
                format!("(List.set({}, {int}.to_u64_wrap({}), {}) ?? crash(\"list-set-at past the end\"))", xs[0], xs[1], xs[2])
            }
            "min" => {
                want(2)?;
                format!("{int}.min({}, {})", xs[0], xs[1])
            }
            "max" => {
                want(2)?;
                format!("{int}.max({}, {})", xs[0], xs[1])
            }
            // `__record-set r "field" v` names the field by a VALUE; when that
            // value is a literal, it is Roc's record update.
            "__record-set" => {
                want(3)?;
                let IrExpr::TextLit(f, _) = args[1] else {
                    return Err("__record-set with a computed field name".into());
                };
                format!("{{ ..{}, {}: {} }}", xs[0], ident_text(f.trim_matches('"'))?, xs[2])
            }
            "__heap-restore" => {
                want(1)?;
                "0".into()
            }
            "int-mod" => {
                want(2)?;
                self.imports.insert("Prelude".into());
                format!("Prelude.int_mod({}, {})", xs[0], xs[1])
            }
            "int-rem" => {
                want(2)?;
                format!("{int}.rem_by({}, {})", xs[0], xs[1])
            }
            // `List Integer -> Text`: each integer's low byte is a unit, as
            // the interpreter's rule says.
            "raw-bytes-to-text" if !self.wgsl => {
                want(1)?;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                format!("CceText.of_bytes({})", xs[0])
            }
            "text-split" => {
                want(2)?;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                format!("CceText.split({}, {})", xs[0], xs[1])
            }
            "list-insert-at" => {
                want(3)?;
                format!(
                    "(List.insert({}, {int}.to_u64_wrap({}), {}) ?? crash(\"list-insert-at past the end\"))",
                    xs[0], xs[1], xs[2]
                )
            }
            "text-compare" => {
                want(2)?;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                format!("CceText.compare({}, {})", xs[0], xs[1])
            }
            "char-code" | "code-to-char" => {
                want(1)?;
                self.imports.insert("CceChar".into());
                format!("CceChar.{}({})", if name == "char-code" { "code" } else { "of_code" }, xs[0])
            }
            "char-code-at" => {
                want(2)?;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                format!("CceText.char_code_at({}, {})", xs[0], xs[1])
            }
            "char-at" => {
                want(2)?;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                format!("CceText.char_at({}, {})", xs[0], xs[1])
            }
            // `char-to-text` keeps the code's low byte and `char-encode` frames
            // it, as the interpreter has them.
            "char-to-text" | "char-encode" => {
                want(1)?;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                let f = if name == "char-to-text" { "char_to_text" } else { "char_encode" };
                format!("CceText.{f}({})", xs[0])
            }
            // The classifiers are code RANGES, not the host's idea of a
            // letter: the alphabet is frequency-ordered (interp.rs).
            "is-letter" | "is-digit" | "is-whitespace" => {
                want(1)?;
                self.imports.insert("CceChar".into());
                format!("CceChar.{}({})", name.replace('-', "_"), xs[0])
            }
            "substring" => {
                want(3)?;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                format!("CceText.substring({}, {}, {})", xs[0], xs[1], xs[2])
            }
            // `__narrow` is the checker's marker for a value proved to fit a
            // bound; at runtime it is the value (interp.rs).
            "__narrow" => {
                want(1)?;
                xs[0].clone()
            }
            // An empty list; the capacity is a reservation, not a length
            // (interp.rs).
            "__list-with-capacity" => {
                want(1)?;
                format!("List.with_capacity({int}.to_u64_wrap({}))", xs[0])
            }
            "list-push" | "list-snoc" => {
                want(2)?;
                format!("List.append({}, {})", xs[0], xs[1])
            }
            // `show` is Codex's own spelling of a value, as units: an integer's
            // digits, `True` or `False`, and a Char's code (interp::show).
            "show" | "integer-to-text" => {
                want(1)?;
                let ty = strip_unit(&args[0].ty()).clone();
                if !matches!(ty, Ty::Text) {
                    self.uses_text = true;
                    self.imports.insert("CceText".into());
                }
                match ty {
                    Ty::Integer(..) if int == "I64" => format!("CceText.show_int({})", xs[0]),
                    Ty::Integer(..) => format!("CceText.show_int({int}.to_i64({}))", xs[0]),
                    Ty::Char => format!("CceText.show_int(CceChar.code({}))", xs[0]),
                    Ty::Boolean => format!(
                        "(if {} {{ {} }} else {{ {} }})",
                        xs[0],
                        crate::roc_text::literal("True"),
                        crate::roc_text::literal("False")
                    ),
                    Ty::Text => xs[0].clone(),
                    // An f32 shows as the double it widens to (real-approx:
                    // `show sum` is `7.0`).
                    Ty::Real(RealWidth::F32, _) if !self.wgsl => {
                        self.imports.insert("Prelude".into());
                        format!("CceText.of_str(Prelude.real_to_str(F32.to_f64({})))", xs[0])
                    }
                    Ty::Real(..) if !self.wgsl => {
                        self.imports.insert("Prelude".into());
                        format!("CceText.of_str(Prelude.real_to_str({}))", xs[0])
                    }
                    other => return Err(format!("show on a {}", crate::ir_text::render_ty(self.syms, &other))),
                }
            }
            // A Codex Text is its units, so its length is their count.
            "text-length" => {
                want(1)?;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                format!("CceText.len({})", xs[0])
            }
            // `text-to-integer` reads the printed text, trimmed, and answers 0
            // for anything it cannot read, as the interpreter does.
            "text-to-integer" => {
                want(1)?;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                format!("CceText.to_integer({})", xs[0])
            }
            "real-from-int" | "__int-to-real" => {
                want(1)?;
                format!("{int}.to_{}({})", real.to_ascii_lowercase(), xs[0])
            }
            "real-to-int" | "__real-to-int" => {
                want(1)?;
                format!("{real}.to_{int_lc}_wrap({})", xs[0])
            }
            "real-abs" => {
                want(1)?;
                format!("{real}.abs({})", xs[0])
            }
            "real-sqrt" => {
                want(1)?;
                format!("{real}.sqrt({})", xs[0])
            }
            "real-max" => {
                want(2)?;
                format!("{real}.max({}, {})", xs[0], xs[1])
            }
            "real-min" => {
                want(2)?;
                format!("{real}.min({}, {})", xs[0], xs[1])
            }
            // `Real approximate` and the overflow modes. A mode is on the
            // operations, so entering or leaving one is the identity; only a
            // change of width converts.
            "to-real-approx" => {
                want(1)?;
                format!("F64.to_f32_wrap({})", xs[0])
            }
            "from-real-approx" => {
                want(1)?;
                format!("F32.to_f64({})", xs[0])
            }
            "to-real-trapping" | "to-real-saturating" | "from-real-trapping" | "from-real-saturating"
            | "to-real-approx-trapping" | "to-real-approx-saturating" | "from-real-approx-trapping"
            | "from-real-approx-saturating" => {
                want(1)?;
                xs[0].clone()
            }
            "real-approx-from-int" => {
                want(1)?;
                format!("I64.to_f32({})", xs[0])
            }
            "real-approx-to-int" => {
                want(1)?;
                format!("F32.to_i64_wrap({})", xs[0])
            }
            "real-approx-to-bits" => {
                want(1)?;
                format!("U32.to_i64(F32.to_bits({}))", xs[0])
            }
            "bits-to-real-approx" => {
                want(1)?;
                format!("F32.from_bits(I64.to_u32_wrap({}))", xs[0])
            }
            "real-to-bits" => {
                want(1)?;
                format!("{uint}.to_{int_lc}_wrap({real}.to_bits({}))", xs[0])
            }
            "bits-to-real" => {
                want(1)?;
                format!("{real}.from_bits({int}.to_{}_wrap({}))", uint.to_ascii_lowercase(), xs[0])
            }
            "bit-and" => {
                want(2)?;
                format!("{int}.bitwise_and({}, {})", xs[0], xs[1])
            }
            "bit-or" => {
                want(2)?;
                format!("{int}.bitwise_or({}, {})", xs[0], xs[1])
            }
            "bit-xor" => {
                want(2)?;
                format!("{int}.bitwise_xor({}, {})", xs[0], xs[1])
            }
            "bit-not" => {
                want(1)?;
                format!("{int}.bitwise_not({})", xs[0])
            }
            // A WGSL shift is a shift; Roc's I32 has them.
            "bit-shl" if self.wgsl => {
                want(2)?;
                format!("I32.shl_wrap({}, I32.to_u8_wrap({}))", xs[0], xs[1])
            }
            "bit-shr" if self.wgsl => {
                want(2)?;
                format!("I32.shr_wrap({}, I32.to_u8_wrap({}))", xs[0], xs[1])
            }
            "bit-shru" if self.wgsl => {
                want(2)?;
                format!("I32.shr_zf_wrap({}, I32.to_u8_wrap({}))", xs[0], xs[1])
            }
            // x86 shifts the word by the count's low six bits: `bit-shr` is
            // `sar`, carrying the sign down, and `bit-shru` is `shr`, filling
            // with zeros (`Builtins.codex`). Roc's shifts take the count
            // modulo the width, so a count's low byte is enough.
            "bit-shl" => {
                want(2)?;
                format!("I64.shl_wrap({}, I64.to_u8_wrap({}))", xs[0], xs[1])
            }
            "bit-shr" => {
                want(2)?;
                format!("I64.shr_wrap({}, I64.to_u8_wrap({}))", xs[0], xs[1])
            }
            "bit-shru" => {
                want(2)?;
                format!("I64.shr_zf_wrap({}, I64.to_u8_wrap({}))", xs[0], xs[1])
            }
            // The builtin spelling of a unary minus, emitted as `E::Negate` is.
            // x86's `abs` tests the sign and negates with a wrapping `neg`
            // (emit-abs-builtin), so the most negative integer answers itself.
            "abs" => {
                want(1)?;
                if self.wgsl {
                    format!("(if {x} < 0 {{ I32.minus_wrap(0, {x}) }} else {{ {x} }})", x = xs[0])
                } else {
                    self.imports.insert("Prelude".into());
                    format!("Prelude.int_abs({})", xs[0])
                }
            }
            "negate" => {
                want(1)?;
                let t = args[0].ty();
                let wrap = self.wgsl || matches!(t, Ty::Integer(_, _, crate::check::Overflow::Wrapping));
                if wrap && matches!(t, Ty::Integer(..)) {
                    format!("{}.minus_wrap(0, {})", self.int(), xs[0])
                } else {
                    format!("(-{})", xs[0])
                }
            }
            // Containment, prefix, suffix and replacement go unit by unit,
            // blind to frames, as the zig parts and the interpreter do.
            "text-contains" | "text-starts-with" | "text-ends-with" => {
                want(2)?;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                let f = match name {
                    "text-contains" => "contains",
                    "text-starts-with" => "starts_with",
                    _ => "ends_with",
                };
                format!("CceText.{f}({}, {})", xs[0], xs[1])
            }
            "text-replace" => {
                want(3)?;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                format!("CceText.replace({}, {}, {})", xs[0], xs[1], xs[2])
            }
            "text-concat-list" => {
                want(1)?;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                format!("CceText.concat_list({})", xs[0])
            }
            // **PRINTING IS WHERE UNITS BECOME UTF-8**, decoded as x86's print
            // loop decodes them (`Text.printed`).
            "print-line-uni" | "print-line" => {
                want(1)?;
                self.uses_line = true;
                self.uses_text = true;
                self.imports.insert("CceText".into());
                format!("line!(CceText.printed({}))", xs[0])
            }
            _ => return Err(format!("builtin `{name}`")),
        })
    }

    fn pattern(&mut self, p: &IrPat, scope: &[&IrExpr]) -> Result<String, String> {
        Ok(match p {
            IrPat::Wild(_) => "_".into(),
            IrPat::Var(n, _, _) => {
                self.locals.push(*n);
                self.binder(*n, scope)?
            }
            IrPat::Lit(v, ty, _) => match strip_unit(ty) {
                Ty::Integer(..) => v.clone(),
                Ty::Char if self.char_match => v.clone(),
                Ty::Char => return Err("a Char pattern inside another pattern".into()),
                Ty::Text => {
                    self.imports.insert("CceText".into());
                    crate::roc_text::literal(v)
                }
                // The IR spells it `True` / `False`; a lowercase test made
                // every boolean pattern `False`, which Roc then called a
                // non-exhaustive match (codex/test/when-bool-cross).
                Ty::Boolean => if v.eq_ignore_ascii_case("true") { "True".into() } else { "False".into() },
                other => return Err(format!("literal pattern of type {}", crate::ir_text::render_ty(self.syms, other))),
            },
            // **A CODEX LIST IS MATCHED WITH Cons AND Nil, A ROC LIST WITH
            // BRACKETS.** The two constructors are the language's, not a
            // chapter's, so a ctor pattern whose type is a list spells the
            // Roc pattern (codex/test's list-pattern).
            IrPat::Ctor(n, subs, ty, _) if matches!(ty, Ty::List(_)) => {
                match (self.syms.text(*n), subs.as_slice()) {
                    ("Nil", []) => "[]".to_string(),
                    ("Cons", [h, t]) => {
                        let head = self.pattern(h, scope)?;
                        let tail = self.pattern(t, scope)?;
                        // A tail nothing reads is `..` alone; `.. as _` is
                        // not a pattern Roc parses.
                        if tail == "_" {
                            format!("[{head}, ..]")
                        } else {
                            format!("[{head}, .. as {tail}]")
                        }
                    }
                    (other, _) => return Err(format!("`{other}` as a list pattern")),
                }
            }
            IrPat::Ctor(n, subs, _, _) => {
                let tag = self.tag(*n)?;
                if subs.is_empty() {
                    tag
                } else {
                    let mut ss = Vec::new();
                    for s in subs {
                        ss.push(self.pattern(s, scope)?);
                    }
                    format!("{tag}({})", ss.join(", "))
                }
            }
            IrPat::Vec_(..) => return Err("vector pattern".into()),
        })
    }
}

impl<'a> Cx<'a> {
    /// The body of a right fold: `if` and `let` keep the mode; an append whose
    /// right operand is the recursive call becomes a step, `helper(args,
    /// List.concat(acc, left))`; any other leaf is the end, `List.concat(acc,
    /// leaf)`, or `acc` alone for an empty list.
    fn fold_expr(&mut self, e: &IrExpr, ind: usize, fold: &Fold) -> Result<String, String> {
        use IrExpr as E;
        match e {
            E::If(c, t, f, _, _) => {
                let c = self.expr(c, ind)?;
                self.fold = Some(fold.clone());
                let t = self.expr(t, ind);
                let f = t.and_then(|t| self.expr(f, ind).map(|f| (t, f)));
                self.fold = None;
                let (t, f) = f?;
                Ok(format!("(if {c} {{ {t} }} else {{ {f} }})"))
            }
            E::Let(..) => {
                let tabs = "\t".repeat(ind + 1);
                let mut out = String::from("({\n");
                let mark = self.locals.len();
                let mut cur = e;
                while let E::Let(n, lty, v, body, _) = cur {
                    let v = self.expr(v, ind + 1)?;
                    self.locals.push(*n);
                    let b = self.binder(*n, &[body])?;
                    out.push_str(&self.local_annotation(&b, lty, &tabs)?);
                    out.push_str(&format!("{tabs}{b} = {v}\n"));
                    cur = body;
                }
                self.fold = Some(fold.clone());
                let last = self.expr(cur, ind + 1);
                self.fold = None;
                out.push_str(&format!("{tabs}{}\n{}}})", last?, "\t".repeat(ind)));
                self.locals.truncate(mark);
                Ok(out)
            }
            E::Apply(f, x, _, _) if fold.push && pushed_onto_self(f, fold.name, &self.push_syms()) => {
                let E::Apply(_, list, _, _) = &**f else { unreachable!() };
                let grown = format!("List.append({}, {})", fold.acc, self.expr(x, ind)?);
                let mut args = Vec::new();
                let mut head = &**list;
                while let E::Apply(g, a, _, _) = head {
                    args.push(&**a);
                    head = g;
                }
                args.reverse();
                let mut xs = Vec::new();
                for a in args {
                    xs.push(self.expr(a, ind)?);
                }
                Ok(format!("{}({}, {grown})", fold.helper, xs.join(", ")))
            }
            other if fold.push => {
                self.imports.insert("Prelude".into());
                Ok(format!("Prelude.push_backwards({}, {})", self.expr(other, ind)?, fold.acc))
            }
            E::Binary(IrBinOp::AppendList, l, r, _, _) if is_self_call(r, fold.name) => {
                let grown = self.grow(&fold.acc, l, ind)?;
                let mut args = Vec::new();
                let mut head = &**r;
                while let E::Apply(f, a, _, _) = head {
                    args.push(&**a);
                    head = f;
                }
                args.reverse();
                let mut xs = Vec::new();
                for a in args {
                    xs.push(self.expr(a, ind)?);
                }
                Ok(format!("{}({}, {grown})", fold.helper, xs.join(", ")))
            }
            other => self.grow(&fold.acc, other, ind),
        }
    }

    /// The builtins that push onto a list (`is_push_fold`).
    fn push_syms(&self) -> Vec<Sym> {
        ["list-push", "list-snoc"].iter().filter_map(|b| self.syms.find(b)).collect()
    }

    /// The accumulator with a list added at its end. **`List.append` PER
    /// ELEMENT WHEN THE LIST IS A LITERAL**: appending one element by
    /// `List.concat(acc, [x])` costs fifty times `List.append(acc, x)`, and
    /// concat of a three-element literal per step goes quadratic (measured,
    /// roc-apps probe/cons). Anything that is not a literal is concatenated.
    fn grow(&mut self, acc: &str, l: &IrExpr, ind: usize) -> Result<String, String> {
        if let IrExpr::List(xs, _, _) = l {
            let mut out = acc.to_string();
            for x in xs {
                out = format!("List.append({out}, {})", self.expr(x, ind)?);
            }
            return Ok(out);
        }
        Ok(format!("List.concat({acc}, {})", self.expr(l, ind)?))
    }
}

/// **A DEFINITION WRITTEN IN ROC, NOT EMITTED FROM ITS CODEX.** Geometry's
/// `geo-sqrt` and Quaternion's `quat-real-sqrt` are Newton's method written out:
/// a guess refined until two guesses are within `~`, four ULPs. Roc's `sqrt` is
/// the machine's instruction; the loop's answer is within those few ULPs of it
/// (`in_roc_tests`). Each keeps its definition's guard, zero for an argument that
/// is not positive, where `sqrt` answers NaN. The chapter is part of the key, so
/// a program's own definition of the same name is emitted as written.
fn in_roc(chapter: &str, name: &str, params: &[String], real: &str) -> Option<String> {
    match (chapter, name, params) {
        ("Geometry", "geo-sqrt", [n]) | ("Quaternion", "quat-real-sqrt", [n]) => {
            Some(format!("|{n}| if {n} <= 0.0 {{ 0.0 }} else {{ {real}.sqrt({n}) }}"))
        }
        // The derived-Ord wrappers over two primitives. Lowering compares
        // through two Integer temporaries (`gen-int-compare`, upstream's
        // too), which Roc rejects for a Bool or a Real; they are written
        // only when nothing prunes them, as `rocemit --whole` does not.
        // False orders before True, as 0 before 1.
        (_, "__compare_Boolean", [x, y]) => {
            Some(format!("|{x}, {y}| if {x} == {y} {{ 0 }} else if {x} {{ 1 }} else {{ -1 }}"))
        }
        (_, "__compare_Real", [x, y]) => {
            Some(format!("|{x}, {y}| if {x} < {y} {{ -1 }} else if {x} > {y} {{ 1 }} else {{ 0 }}"))
        }
        _ => None,
    }
}

#[cfg(test)]
mod in_roc_tests {
    use super::in_roc;

    /// Codex's `~`: the bit patterns as monotone ordinals, within four.
    fn ordinal(f: f64) -> i64 {
        let b = f.to_bits() as i64;
        if b < 0 { (b ^ i64::MAX).wrapping_add(1) } else { b }
    }

    /// `geo-sqrt` as Geometry writes it.
    fn newton(n: f64) -> f64 {
        if n <= 0.0 {
            return 0.0;
        }
        let mut guess = n / 2.0 + 1.0;
        loop {
            let next = (guess + n / guess) / 2.0;
            if (ordinal(next) - ordinal(guess)).abs() <= 4 {
                return next;
            }
            guess = next;
        }
    }

    #[test]
    fn both_newton_roots_are_written_as_roc_sqrt_behind_their_guard() {
        let n = vec!["n".to_string()];
        let want = "|n| if n <= 0.0 { 0.0 } else { F64.sqrt(n) }";
        assert_eq!(in_roc("Geometry", "geo-sqrt", &n, "F64").as_deref(), Some(want));
        assert_eq!(in_roc("Quaternion", "quat-real-sqrt", &n, "F64").as_deref(), Some(want));
        assert_eq!(in_roc("Raytracer", "geo-sqrt", &n, "F64"), None);
        assert_eq!(in_roc("Geometry", "geo-sqrt-loop", &n, "F64"), None);
    }

    /// The loop and the instruction agree to within four ULPs, from a
    /// millionth to a trillion and on every perfect square the scenes use.
    #[test]
    fn the_newton_loop_is_within_four_ulps_of_sqrt() {
        let mut worst = 0;
        let mut x = 1e-6_f64;
        while x < 1e12 {
            for n in [x, x * 1.37, x * 7.91] {
                worst = worst.max((ordinal(newton(n)) - ordinal(n.sqrt())).abs());
            }
            x *= 3.3;
        }
        for k in 1..2000 {
            let n = (k * k) as f64;
            worst = worst.max((ordinal(newton(n)) - ordinal(n.sqrt())).abs());
        }
        assert!(worst <= 4, "the loop is {worst} ULPs from sqrt somewhere");
    }
}

/// Whether `e` is `name a b ..`: an application spine headed by the name.
fn is_self_call(e: &IrExpr, name: Sym) -> bool {
    let mut head = e;
    while let IrExpr::Apply(f, _, _, _) = head {
        head = f;
    }
    matches!(head, IrExpr::Name(n, _, _) if *n == name) && matches!(e, IrExpr::Apply(..))
}

fn calls(e: &IrExpr, name: Sym) -> bool {
    uses(e, name)
}

/// A body that builds its list by appending a recursive call: every
/// recursive call is the right operand of an append at a leaf of the
/// if/let tree, its arguments make no recursive call, and there is at least
/// one. The shape is what the accumulator rewrite in `Cx::def` relies on.
fn is_right_fold(body: &IrExpr, name: Sym) -> bool {
    fn leaves(e: &IrExpr, name: Sym, found: &mut bool) -> bool {
        use IrExpr as E;
        match e {
            E::If(c, t, f, _, _) => !calls(c, name) && leaves(t, name, found) && leaves(f, name, found),
            E::Let(_, _, v, b, _) => !calls(v, name) && leaves(b, name, found),
            E::Binary(IrBinOp::AppendList, l, r, _, _) if is_self_call(r, name) => {
                let mut args_ok = true;
                let mut head = &**r;
                while let E::Apply(f, a, _, _) = head {
                    args_ok &= !calls(a, name);
                    head = f;
                }
                *found = true;
                !calls(l, name) && args_ok
            }
            other => !calls(other, name),
        }
    }
    let mut found = false;
    matches!(body.ty(), Ty::List(_)) && leaves(body, name, &mut found) && found
}

/// Whether `name` builds its list by pushing onto its own recursive call,
/// `list-push (name ..) x`: every recursive call is the list a push extends,
/// at a leaf of the if-tree, and nowhere else. `push` holds the builtins that
/// push (`list-push`, `list-snoc`).
fn is_push_fold(body: &IrExpr, name: Sym, push: &[Sym]) -> bool {
    fn leaves(e: &IrExpr, name: Sym, push: &[Sym], found: &mut bool) -> bool {
        use IrExpr as E;
        match e {
            E::If(c, t, f, _, _) => !calls(c, name) && leaves(t, name, push, found) && leaves(f, name, push, found),
            E::Let(_, _, v, b, _) => !calls(v, name) && leaves(b, name, push, found),
            E::Apply(f, x, _, _) if pushed_onto_self(f, name, push) => {
                let E::Apply(_, list, _, _) = &**f else { return false };
                let mut args_ok = true;
                let mut head = &**list;
                while let E::Apply(g, a, _, _) = head {
                    args_ok &= !calls(a, name);
                    head = g;
                }
                *found = true;
                !calls(x, name) && args_ok
            }
            other => !calls(other, name),
        }
    }
    let mut found = false;
    matches!(body.ty(), Ty::List(_)) && leaves(body, name, push, &mut found) && found
}

/// Whether `f` is a push applied to a recursive call: `list-push (name ..)`.
fn pushed_onto_self(f: &IrExpr, name: Sym, push: &[Sym]) -> bool {
    match f {
        IrExpr::Apply(h, list, _, _) => matches!(&**h, IrExpr::Name(n, _, _) if push.contains(n)) && is_self_call(list, name),
        _ => false,
    }
}

fn uses(e: &IrExpr, n: Sym) -> bool {
    let mut found = false;
    e.walk(&mut |x| {
        if let IrExpr::Name(m, _, _) = x {
            if *m == n {
                found = true;
            }
        }
    });
    found
}

/// How many parameters a function type takes in Roc, where `fun_parts`
/// writes the whole curried chain as one signature.
fn arrows_of(t: &Ty) -> usize {
    match t {
        Ty::Fun(_, _, r) => 1 + arrows_of(r),
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => arrows_of(b),
        _ => 0,
    }
}

/// A type with its unit taken off: the number a unit value is at run time.
fn strip_unit(t: &Ty) -> &Ty {
    match t {
        Ty::Unit(_, inner) => strip_unit(inner),
        other => other,
    }
}

/// Whether the emitted text reads `n`: a mention anywhere but as the
/// argument of `restore`, whose argument is not emitted.
fn reads(e: &IrExpr, n: Sym, restore: Option<Sym>) -> bool {
    let (mut all, mut marks) = (0, 0);
    e.walk(&mut |x| match x {
        IrExpr::Name(m, _, _) if *m == n => all += 1,
        IrExpr::Apply(f, a, _, _)
            if matches!(**f, IrExpr::Name(r, _, _) if Some(r) == restore)
                && matches!(**a, IrExpr::Name(m, _, _) if m == n) =>
        {
            marks += 1
        }
        _ => {}
    });
    all > marks
}

/// A Codex name as a Roc identifier: kebab to snake, keywords suffixed. A
/// lifted `__lam_0` loses its underscores, which in Roc would mark it unused,
/// and a derived `__eq_Tup2` loses its capitals, which Roc reads as a type.
/// Past a `let x = e in x`, which is `e`.
///
/// **A NAME THAT ONLY CARRIES A TYPE IS NOT A BINDING.** An IR literal has
/// no type slot, so lowering binds a unit-typed value to a name and answers
/// the name, the name being where the unit type can live
/// (`Lowering.codex:615`, `lower_unit_ctor_value`). Roc spells a unit as its
/// own integer and needs no such name; emitting one wrote a binding nothing
/// reads, spelled `__unit-<offset>` from the value's offset in the BUNDLED
/// source -- so the same chapter emitted different text behind different
/// chapters, and roc-apps, which shares one copy of each chapter across the
/// tests, could not share those.
fn carried_value(e: &IrExpr) -> &IrExpr {
    let IrExpr::Let(n, _, v, body, _) = e else { return e };
    match &**body {
        IrExpr::Name(m, _, _) if m == n => carried_value(v),
        _ => e,
    }
}

fn ident_text(t: &str) -> Result<String, String> {
    let t = t.trim_start_matches('_');
    if t.is_empty() {
        return Err("a name of only underscores cannot be a Roc identifier".into());
    }
    if !t.chars().all(|c| c.is_ascii_alphanumeric() || matches!(c, '-' | '_' | '[' | ']' | ',')) {
        return Err(format!("name `{t}` cannot be a Roc identifier"));
    }
    // An instance for an applied head is named by its KEY, `to-text-List[Integer]`
    // (`type-key-of`), and Roc has no brackets in a name: spelled out.
    let t = t.replace('[', "-of-").replace(',', "-and-").replace(']', "-end");
    // **ONLY THE FIRST LETTER IS LOWERCASED.** Roc wants a value name to
    // start lowercase and allows capitals after that, and Codex tells two
    // names apart by case: `test-glyph-e` and `test-glyph-E` are both in
    // codex/test's ui-font-test, and lowercasing the whole name made them
    // one definition, so the program printed the second one's answer for
    // both. A derived `__eq_Tup2` still needs its leading capital lowered,
    // which is what this was for.
    let s = t.replace('-', "_");
    let mut cs = s.chars();
    let s: String = match cs.next() {
        Some(c) => c.to_ascii_lowercase().to_string() + cs.as_str(),
        None => s,
    };
    Ok(if KEYWORDS.contains(&s.as_str()) { format!("{s}_") } else { s })
}

fn int_lit(v: i64) -> String {
    if v < 0 {
        format!("({v})")
    } else {
        v.to_string()
    }
}

/// The IR carries a Real's BITS. Roc reads back the shortest round-tripping
/// decimal exactly; a value that would need an exponent, or is not finite,
/// goes through `F64.from_bits` instead.
fn num_lit(bits: i64, f32: bool) -> String {
    let f = f64::from_bits(bits as u64);
    if f32 {
        // The plug's WGSL reads the same decimal as an f32; so does Roc.
        let g = f as f32;
        if !g.is_finite() {
            return format!("F32.from_bits({})", g.to_bits());
        }
        let s = format!("{g:?}");
        if s.contains('e') {
            return format!("F32.from_bits({})", g.to_bits());
        }
        return if g.is_sign_negative() { format!("({s})") } else { s };
    }
    if !f.is_finite() {
        return format!("F64.from_bits({})", bits as u64);
    }
    let s = format!("{f:?}");
    if s.contains('e') {
        return format!("F64.from_bits({})", bits as u64);
    }
    if f.is_sign_negative() {
        format!("({s})")
    } else {
        s
    }
}

#[cfg(test)]
mod literals_round_trip {
    use super::num_lit;

    #[test]
    fn the_fourth_case_keeps_its_digits() {
        let bits = 0.012500000000000011_f64.to_bits() as i64;
        assert_eq!(num_lit(bits, false), "0.012500000000000011");
    }

    #[test]
    fn a_negative_is_parenthesised() {
        assert_eq!(num_lit((-0.25_f64).to_bits() as i64, false), "(-0.25)");
    }

    #[test]
    fn an_exponent_goes_through_bits() {
        assert_eq!(num_lit(1e21_f64.to_bits() as i64, false), format!("F64.from_bits({})", 1e21_f64.to_bits()));
    }
}

#[cfg(test)]
mod module_names {
    use super::{claim_module, module_name, module_slug};
    use std::collections::BTreeMap;

    #[test]
    fn a_chapter_name_becomes_one_capitalised_word() {
        assert_eq!(module_slug("Foreword--ListUtils"), "ListUtils");
        assert_eq!(module_slug("With-Timeout Test"), "WithTimeoutTest");
        assert_eq!(module_slug("TextSearch Test"), "TextSearchTest");
        assert_eq!(module_slug("List O1 Probe"), "ListO1Probe");
        assert_eq!(module_name(&module_slug("Bounded Integer Ops")).unwrap(), "BoundedIntegerOps");
    }

    #[test]
    fn a_name_with_no_roc_module_in_it_is_still_refused() {
        assert!(module_name(&module_slug("2048 Board")).is_err());
        assert!(module_name(&module_slug("Привет")).is_err());
    }

    #[test]
    fn two_chapters_that_become_one_module_are_refused() {
        let (mut slugs, mut of) = (Vec::new(), BTreeMap::new());
        claim_module(&mut slugs, &mut of, "Core--Maybe").unwrap();
        claim_module(&mut slugs, &mut of, "Core--Maybe").unwrap();
        let e = claim_module(&mut slugs, &mut of, "Emit--Maybe").unwrap_err();
        assert!(e.contains("`Core--Maybe`") && e.contains("`Emit--Maybe`"), "{e}");
        assert_eq!(slugs, vec!["Maybe"]);
    }
}

/// A record declaration with a field type naming a type variable that is not
/// one of the record's own parameters: a lowercase name in type position.
fn has_free_field_binder(td: &crate::ast::TypeDef, syms: &SymTab) -> bool {
    use crate::ast::{TypeDef, TypeExpr as T};
    fn free(t: &T, params: &[Sym], syms: &SymTab) -> bool {
        match t {
            T::Named(n, _) => syms.text(*n).starts_with(|c: char| c.is_ascii_lowercase()) && !params.contains(n),
            T::Fun(a, r, _) | T::PropEq(a, r, _) => free(a, params, syms) || free(r, params, syms),
            T::App(c, args, _) => free(c, params, syms) || args.iter().any(|x| free(x, params, syms)),
            T::Effect(_, _, _, r, _) | T::Linear(r, _) | T::BoundedInt(r, ..) | T::Constrained(_, _, r, _) => free(r, params, syms),
            T::Forall(v, vt, p, _) => {
                let mut inner = params.to_vec();
                inner.push(*v);
                free(vt, &inner, syms) || free(p, &inner, syms)
            }
        }
    }
    match td {
        TypeDef::Record(_, params, fields, ..) => fields.iter().any(|f| free(&f.type_expr, params, syms)),
        _ => false,
    }
}

/// **A LIST HELPER CALL IS ROC'S `==`, AND SO IS A GENERIC RECORD'S.** Since
/// U64 the desugarer derives `__eq_<R>` for a record too, and for one with
/// type parameters Roc needs a `where` clause per parameter, which this
/// emitter does not write (see the nominal-record note above): such a helper
/// is dropped, and its calls, bare or instantiated (`__eq_R@...`), are Roc's
/// structural `==`, which is what rocemit wrote before U64.
///
/// Since U64's step 1 lowering calls
/// `__eq_List@<T>` for `==` on a list, as upstream does, and `eq_helpers`
/// mints its definition only on the driver's path; rocemit reads the chapter
/// whole and gets the call alone. In Roc a list compares structurally, each
/// element by its own `is_eq`, so the call is put back as the `binary eq`
/// rocemit always wrote for it -- and `/=` stays the `if` lowering made of
/// it. Done before anything reads the IR, so the `where`-clause walk and the
/// effect threading see exactly what they saw before.
pub fn restore_list_eq(defs: Vec<IrDef>, syms: &SymTab, ch: &Chapter) -> Vec<IrDef> {
    let generic: Vec<String> = ch
        .type_defs
        .iter()
        .filter_map(|td| match td {
            TypeDef::Record(n, ps, ..) if !ps.is_empty() => Some(format!("__eq_{}", syms.text(*n))),
            _ => None,
        })
        .collect();
    let plain_eq = |n: &str| n.starts_with("__eq_List@") || generic.iter().any(|g| n == g || n.starts_with(&format!("{g}@")));
    defs.into_iter()
        .filter(|d| !generic.iter().any(|g| syms.text(d.name) == g))
        .map(|mut d| {
            d.body = list_eq_expr(&d.body, syms, &plain_eq);
            d
        })
        .collect()
}

fn list_eq_expr(e: &IrExpr, syms: &SymTab, plain_eq: &dyn Fn(&str) -> bool) -> IrExpr {
    use IrExpr as E;
    let list_eq_expr = |x: &IrExpr, syms: &SymTab| list_eq_expr(x, syms, plain_eq);
    let go = |x: &IrExpr| Box::new(list_eq_expr(x, syms));
    let stmts = |ss: &[IrActStmt]| -> Vec<IrActStmt> {
        ss.iter()
            .map(|s| match s {
                IrActStmt::Bind(n, t, x, sp) => IrActStmt::Bind(*n, t.clone(), list_eq_expr(x, syms), *sp),
                IrActStmt::Exec(x, sp) => IrActStmt::Exec(list_eq_expr(x, syms), *sp),
            })
            .collect()
    };
    match e {
        E::Apply(f, b, t, sp) => {
            if let E::Apply(h, a, _, _) = &**f {
                if let E::Name(n, _, _) = &**h {
                    if plain_eq(syms.text(*n)) {
                        return E::Binary(IrBinOp::Eq, go(a), go(b), t.clone(), *sp);
                    }
                }
            }
            E::Apply(go(f), go(b), t.clone(), *sp)
        }
        E::Binary(op, l, r, t, sp) => E::Binary(*op, go(l), go(r), t.clone(), *sp),
        E::Negate(x, t, sp) => E::Negate(go(x), t.clone(), *sp),
        E::If(c, a, b, t, sp) => E::If(go(c), go(a), go(b), t.clone(), *sp),
        E::Let(n, t, v, b, sp) => E::Let(*n, t.clone(), go(v), go(b), *sp),
        E::Lambda(ps, b, t, sp) => E::Lambda(ps.clone(), go(b), t.clone(), *sp),
        E::List(xs, t, sp) => E::List(xs.iter().map(|x| list_eq_expr(x, syms)).collect(), t.clone(), *sp),
        E::Match(s, bs, t, sp) => E::Match(
            go(s),
            bs.iter()
                .map(|b| crate::ir_chapter::IrBranch {
                    pattern: b.pattern.clone(),
                    body: list_eq_expr(&b.body, syms),
                    guard: list_eq_expr(&b.guard, syms),
                    span: b.span,
                })
                .collect(),
            t.clone(),
            *sp,
        ),
        E::Act(ss, t, sp) => E::Act(stmts(ss), t.clone(), *sp),
        E::Record(n, fs, t, sp) => E::Record(
            *n,
            fs.iter().map(|f| crate::ir_chapter::IrFieldVal { name: f.name, value: list_eq_expr(&f.value, syms) }).collect(),
            t.clone(),
            *sp,
        ),
        E::FieldAccess(r, f, t, sp) => E::FieldAccess(go(r), f.clone(), t.clone(), *sp),
        E::FieldStore(r, f, v, t, sp) => E::FieldStore(go(r), f.clone(), go(v), t.clone(), *sp),
        E::Handle(eff, h, cs, t, sp) => E::Handle(
            eff.clone(),
            go(h),
            cs.iter()
                .map(|c| crate::ir_chapter::IrHandleClause {
                    op_name: c.op_name.clone(),
                    params: c.params.clone(),
                    resume_name: c.resume_name,
                    body: list_eq_expr(&c.body, syms),
                    span: c.span,
                })
                .collect(),
            t.clone(),
            *sp,
        ),
        E::WithTimeout(s, es, sc, b, t, sp) => E::WithTimeout(*s, es.clone(), sc.clone(), go(b), t.clone(), *sp),
        E::Try(m, b, f, x, t, sp) => E::Try(*m, stmts(b), stmts(f), stmts(x), t.clone(), *sp),
        other => other.clone(),
    }
}
