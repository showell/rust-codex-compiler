//! THE COMPILER'S OWN ALLOCATOR, MODELLED. Upstream calls it the phase
//! allocator: a bump heap with a deck growing under it, `__heap-advance` to
//! reserve, `__heap-restore` to give back, and `phase-compact` between phases.
//!
//! **IT WAS ARITHMETIC AND NOTHING ELSE, AND THE COMPILER NOTICED.** Two
//! counters answered `__heap-save` and `__deck-pos` correctly while the values
//! themselves lived wherever the host put them, which is fine until the
//! compiler asks a question that relates the two:
//!
//! ```text
//! copy-sx-text (b) (t) = if address-of t < b then t else substring t 0 (text-length t)
//! ```
//!
//! That is a DURABILITY test -- was this text allocated before the base `b`,
//! and therefore safe to share rather than rebuild. Answered with a host
//! pointer against an allocator offset it is false for every text, always, so
//! nothing was ever durable and the source text was rebuilt at every keep
//! boundary: 24,350 copies averaging 89 KB, which was the whole of a 2.3 GB
//! peak on a 112 KB subject.
//!
//! So addresses have to come from HERE, from the same counter `__heap-save`
//! reads. That is what this module is for, and it is deliberately separate
//! from the interpreter: the arithmetic is worth being able to test without a
//! program to run.

/// Everything is eight-byte aligned, because everything upstream is a word.
/// A text of nine bytes occupies sixteen, and two allocations never overlap.
const ALIGN: i64 = 8;

pub fn aligned(n: i64) -> i64 {
    (n + ALIGN - 1) / ALIGN * ALIGN
}

/// **THE HEAP DOES NOT START AT ZERO, and neither does anybody else's.** The
/// zig plug opens its cursor at 6,291,456 and everything under it belongs to
/// the deck; bare metal's heap sits above the loaded image. Two things here
/// need that gap. A text LITERAL lives in the image, below the heap, which is
/// why it is durable and shared rather than copied -- so literals are handed
/// addresses from the band below this origin. And zero has to stay available
/// as "not an address at all", which it cannot be if it is also the first
/// thing allocated.
pub const HEAP_ORIGIN: i64 = 16 << 20;

/// Where literal addresses start. Above zero because zero means "no address",
/// and below `HEAP_ORIGIN` because a literal is durable against every base the
/// compiler can compute.
pub const IMAGE_ORIGIN: i64 = 8;

/// **A LITERAL IS INTERNED, NOT ALLOCATED**, and it is done here rather than
/// on a `Bump` because literals are built when a chapter is COMPILED and the
/// interpreter that will run it does not exist yet. That is faithful rather
/// than convenient: a literal lives in the loaded image on bare metal, one
/// region for the whole program, never reclaimed and below every heap address
/// -- which is precisely why `copy-sx-text` shares one instead of rebuilding
/// it.
///
/// Process-wide, so two interpreters in one process draw from one image, which
/// is what a process has. Distinctness is what the address is for and that
/// survives sharing; the band holds two million literals before the assert
/// fires, against roughly fifty thousand in the compiler's own bundle.
pub fn intern_literal(n: i64) -> i64 {
    use std::sync::atomic::{AtomicI64, Ordering::Relaxed};
    static NEXT: AtomicI64 = AtomicI64::new(IMAGE_ORIGIN);
    let at = NEXT.fetch_add(aligned(n).max(ALIGN), Relaxed);
    debug_assert!(at < HEAP_ORIGIN, "the image band ran into the heap");
    at
}

/// The two cursors and the extent depth between them.
#[derive(Debug, Clone)]
pub struct Bump {
    /// The image cursor: literals, which never move and are never reclaimed.
    image: i64,
    /// Where the cursor sits outside an extent.
    bivy: i64,
    /// The deck-pos CELL, which `__deck-pos` reads and `__deck-set` writes.
    cell: i64,
    /// The cursor while an extent is open, loaded from the cell on the way in
    /// and written back on the way out, both only at a zero crossing.
    deck: i64,
    /// How many extents are open.
    depth: u32,
    /// The furthest the active cursor ever reached.
    pub hwm: i64,
}

impl Default for Bump {
    fn default() -> Bump {
        Bump { image: IMAGE_ORIGIN, bivy: HEAP_ORIGIN, cell: HEAP_ORIGIN, deck: HEAP_ORIGIN, depth: 0, hwm: HEAP_ORIGIN }
    }
}

impl Bump {
    /// A literal's address, from the band below the heap. It is not reclaimed
    /// and it is durable against every base, which is what a literal is.
    pub fn intern(&mut self, n: i64) -> i64 {
        let at = self.image;
        self.image += aligned(n).max(ALIGN);
        debug_assert!(self.image < HEAP_ORIGIN, "the image band ran into the heap");
        at
    }

    /// The ACTIVE cursor: inside an extent the deck, outside it the bivy.
    ///
    /// This is the whole of what makes a guarded copy's
    /// `__heap-save >= ceiling` mean anything -- the guard asks about the
    /// region it is writing into, and which region that is depends on the
    /// bracket it is standing in.
    pub fn cursor(&self) -> i64 {
        if self.depth == 0 {
            self.bivy
        } else {
            self.deck
        }
    }

    pub fn set_cursor(&mut self, v: i64) {
        if v > self.hwm {
            self.hwm = v;
        }
        if self.depth == 0 {
            self.bivy = v;
        } else {
            self.deck = v;
        }
    }

    /// **RESERVE `n` BYTES AND ANSWER WHERE THEY START.** This is what makes
    /// an address an address: the answer is the cursor before the bump, so it
    /// is below every address handed out after it and at or above every one
    /// before, which is exactly the ordering `address-of t < b` asks about.
    pub fn alloc(&mut self, n: i64) -> i64 {
        let at = self.cursor();
        self.set_cursor(at + aligned(n));
        at
    }

    pub fn deck_pos(&self) -> i64 {
        self.cell
    }

    pub fn deck_set(&mut self, v: i64) {
        self.cell = v;
    }

    /// Open an extent. Only the outermost pair copies the cell into the deck
    /// cursor; a nested `deck-record` inside one already open must not reset
    /// the cursor its caller is filling.
    pub fn enter(&mut self) {
        if self.depth == 0 {
            self.deck = self.cell;
        }
        self.depth += 1;
    }

    /// Close one, writing the cursor back only at the zero crossing.
    pub fn exit(&mut self) {
        self.depth = self.depth.saturating_sub(1);
        if self.depth == 0 {
            self.cell = self.deck;
        }
    }

    pub fn depth(&self) -> u32 {
        self.depth
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A word at a time, so a nine-byte text occupies sixteen and the next
    /// allocation starts on a boundary.
    #[test]
    fn every_allocation_is_word_aligned() {
        assert_eq!((aligned(0), aligned(1), aligned(8), aligned(9)), (0, 8, 8, 16));
    }

    /// **THE ADDRESS IS THE CURSOR BEFORE THE BUMP**, which is what makes the
    /// ordering mean something: everything allocated earlier is below,
    /// everything later is above.
    #[test]
    fn an_allocation_answers_where_it_starts_and_moves_the_cursor_past_it() {
        let mut b = Bump::default();
        assert_eq!(b.alloc(24), HEAP_ORIGIN);
        assert_eq!(b.cursor(), HEAP_ORIGIN + 24);
        assert_eq!(b.alloc(1), HEAP_ORIGIN + 24);
        assert_eq!(b.cursor(), HEAP_ORIGIN + 32, "one byte still costs a word");
    }

    /// The ordering the compiler's durability test is asking about.
    #[test]
    fn earlier_allocations_are_below_a_later_base() {
        let mut b = Bump::default();
        let early = b.alloc(100);
        let base = b.cursor();
        let late = b.alloc(100);
        assert!(early < base, "allocated before the base, so it is durable");
        assert!(late >= base, "allocated after it, so it is not");
    }

    /// **INSIDE AN EXTENT THE DECK MOVES AND THE BIVY DOES NOT.** `deck-record`
    /// is how the compiler puts a value somewhere its caller's bracket will
    /// keep, and an allocation made inside one that came off the bivy would be
    /// reclaimed while the record it belongs to survives.
    #[test]
    fn an_allocation_inside_an_extent_comes_off_the_deck() {
        let mut b = Bump::default();
        b.deck_set(1000);
        b.alloc(64);
        let bivy_before = b.cursor();
        b.enter();
        let inside = b.alloc(32);
        b.exit();
        assert_eq!(inside, 1000, "off the deck cell, not off the bivy");
        assert_eq!(b.cursor(), bivy_before, "the bivy did not move");
        assert_eq!(b.deck_pos(), 1032, "and the cell carries the deck's new position");
    }

    /// Only the outermost pair copies, so a nested extent does not reset the
    /// cursor the outer one is filling.
    #[test]
    fn only_the_outermost_extent_copies_the_cell() {
        let mut b = Bump::default();
        b.deck_set(500);
        b.enter();
        let first = b.alloc(16);
        b.enter();
        let nested = b.alloc(16);
        b.exit();
        let after = b.alloc(16);
        b.exit();
        assert_eq!((first, nested, after), (500, 516, 532));
        assert_eq!(b.deck_pos(), 548);
    }

    /// **A RESTORE HANDS THE SAME ADDRESSES OUT AGAIN, and that is faithful
    /// rather than a bug.** It is how a phase reuses its scratch, and it is
    /// also how a value that outlives the bracket that made it comes to share
    /// an address with whatever was allocated next. Modelling it is the only
    /// way this arm could ever see that happen.
    #[test]
    fn a_restore_hands_the_same_addresses_out_again() {
        let mut b = Bump::default();
        let mark = b.cursor();
        let first = b.alloc(40);
        b.set_cursor(mark);
        let second = b.alloc(40);
        assert_eq!(first, second, "the scratch was reused, exactly as upstream reuses it");
    }

    /// **A LITERAL IS BELOW THE HEAP AND THEREFORE DURABLE**, which is the
    /// property `copy-sx-text` reads to decide whether to share a text or
    /// rebuild it. Distinct, non-zero, and under every base the compiler can
    /// compute, because every base comes off a cursor that starts at the
    /// heap origin.
    #[test]
    fn a_literal_is_below_every_heap_address() {
        let mut b = Bump::default();
        let (one, two) = (b.intern(13), b.intern(13));
        let allocated = b.alloc(8);
        assert_ne!(one, two, "two literals are two addresses");
        assert!(one > 0 && two > 0, "and neither is the not-an-address sentinel");
        assert!(two < allocated, "both below anything the heap hands out");
        assert!(two < b.cursor() && one < HEAP_ORIGIN);
    }

    /// Nothing is ever allocated at zero, so zero can go on meaning what the
    /// compiler reads it as: not an address.
    #[test]
    fn zero_is_never_a_live_address() {
        let mut b = Bump::default();
        assert_ne!(b.intern(1), 0);
        assert_ne!(b.alloc(1), 0);
        assert_eq!(b.cursor() > HEAP_ORIGIN, true);
    }

    /// The high-water mark survives a restore, because it is about how much
    /// was ever needed and not about how much is held.
    #[test]
    fn the_high_water_mark_remembers_what_a_restore_gave_back() {
        let mut b = Bump::default();
        b.alloc(4096);
        b.set_cursor(HEAP_ORIGIN);
        assert_eq!(b.cursor(), HEAP_ORIGIN);
        assert_eq!(b.hwm, HEAP_ORIGIN + 4096);
    }
}
