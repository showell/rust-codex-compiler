//! Interned names: a `Sym` is an index, and the text lives once in a `SymTab`.
//!
//! **A name used to be a `String`, allocated once per OCCURRENCE.** Desugaring
//! the corpus called `Desugar::text` 6,185,699 times and copied 32.3 MB to do
//! it, for 50,275 distinct strings -- and even per file, where nothing is
//! shared between chapters, the ratio is 12.5 to 1 on a large unit and 6.7 to
//! 1 on a median one. The pass was a third allocator and a fifth kernel,
//! backing memory for those copies.
//!
//! So a name is four bytes now. Three things follow, and the third is the one
//! that is easy to miss:
//!
//! * **it is `Copy`**, so passing a name around costs nothing and no clone
//!   appears anywhere;
//! * **it compares as an integer**, which is what `scope` and `check` do to
//!   names constantly -- a `HashSet<Sym>` hashes four bytes, not a string;
//! * **it shrinks every node that holds one.** `Expr` is as large as its
//!   largest variant and every pass moves 6.58M of them, so a name going 24
//!   bytes to 4 is felt by the whole tree, not just by names.
//!
//! **The text is not reachable from a `Sym`.** That is deliberate rather than
//! awkward: the alternative -- a global table, or leaking the strings to get
//! `&'static str` -- is how this is usually done, and it needs `unsafe` or a
//! lock on the hot path. This repo has neither, and a `SymTab` threaded to the
//! places that actually print a name turned out to be a dozen signatures.
//! `Chapter` owns the table for its own names, so anything holding a chapter
//! already has it.

use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};

/// FNV-1a, for the interner's table only.
///
/// **The default hasher is SipHash, which is the wrong tool here.** It is
/// built to survive an adversary choosing keys; these keys are identifiers out
/// of a source file, and there is no adversary. Interning runs 6.19 million
/// times over the corpus on strings averaging five bytes, so the hash IS the
/// cost -- swapping an allocation for a SipHash is a wash, which is exactly
/// what the first measurement showed.
#[derive(Default)]
pub struct Fnv(u64);

impl Hasher for Fnv {
    fn write(&mut self, bytes: &[u8]) {
        let mut h = if self.0 == 0 { 0xcbf2_9ce4_8422_2325 } else { self.0 };
        for b in bytes {
            h ^= *b as u64;
            h = h.wrapping_mul(0x1000_0000_01b3);
        }
        self.0 = h;
    }
    fn finish(&self) -> u64 {
        self.0
    }
}

type FnvMap<K, V> = HashMap<K, V, BuildHasherDefault<Fnv>>;

/// A name, as an index into the `SymTab` that interned it.
///
/// **A `Sym` is only meaningful against the table that made it.** Mixing two
/// tables silently reads the wrong name rather than failing, so a `SymTab`
/// travels with the tree it belongs to -- in practice inside `Chapter`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Sym(u32);

/// The empty name, which every table interns first.
///
/// The desugarer reaches for it whenever a name-shaped token is missing --
/// `unwrap_or_default()` on a malformed definition -- so it has to exist
/// before anything else is interned, and it has to be the same index in every
/// table. `SymTab::default` is what guarantees that, and `empty_is_zero`
/// checks it.
impl Default for Sym {
    fn default() -> Sym {
        Sym(0)
    }
}

#[derive(Clone, Debug)]
pub struct SymTab {
    text: Vec<String>,
    index: FnvMap<String, Sym>,
}

impl Default for SymTab {
    fn default() -> SymTab {
        let mut t = SymTab { text: Vec::new(), index: FnvMap::default() };
        t.intern("");
        t
    }
}

impl SymTab {
    pub fn intern(&mut self, s: &str) -> Sym {
        if let Some(&i) = self.index.get(s) {
            return i;
        }
        let i = Sym(self.text.len() as u32);
        self.text.push(s.to_string());
        self.index.insert(s.to_string(), i);
        i
    }

    /// The text of a name this table interned.
    ///
    /// Out of range is a bug in the caller -- a `Sym` from another table -- and
    /// it says so rather than returning something plausible.
    pub fn text(&self, s: Sym) -> &str {
        self.text.get(s.0 as usize).map(String::as_str).unwrap_or("<not this table>")
    }

    /// The symbol for a name already interned, without interning it. Callers
    /// that only want to ASK about a name use this: interning from a lookup
    /// grows the table with names the tree does not contain.
    pub fn find(&self, s: &str) -> Option<Sym> {
        self.index.get(s).copied()
    }

    pub fn len(&self) -> usize {
        self.text.len()
    }

    pub fn is_empty(&self) -> bool {
        self.text.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_is_zero() {
        let t = SymTab::default();
        assert_eq!(t.text(Sym::default()), "");
        assert_eq!(t.find(""), Some(Sym::default()));
    }

    #[test]
    fn same_text_is_the_same_symbol() {
        let mut t = SymTab::default();
        let a = t.intern("list-at");
        let b = t.intern("list-at");
        assert_eq!(a, b);
        assert_ne!(a, t.intern("list-atx"));
        assert_eq!(t.text(a), "list-at");
    }

    #[test]
    fn a_symbol_from_another_table_is_named_as_such() {
        let (mut a, b) = (SymTab::default(), SymTab::default());
        let far = a.intern("only-in-a");
        assert_eq!(b.text(far), "<not this table>");
    }
}
