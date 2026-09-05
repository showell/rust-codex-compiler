//! **HOW MUCH MEMORY A PROGRAM NEEDED**, which is the number the interpreter
//! could not answer.
//!
//! Not peak RSS. RSS is the process, and the process holds a 3.4 MB compiler
//! subject, its AST, and whatever the allocator has not returned to the
//! kernel; it also only ever rises, so a second program in the same process
//! reports the first one's high-water mark. What is wanted is what THIS
//! program asked for, resettable between programs and attributable to the
//! interpreter rather than to the host.
//!
//! So this is a global allocator that counts. Two relaxed atomics, one add per
//! allocation and one subtract per free, and a peak that only moves on the way
//! up. Measured on the whole safari suite -- 54 chapters, 2,351 graded values
//! -- the cost is in the noise against the same suite without it.
//!
//! RELAXED IS THE RIGHT ORDERING and not a shortcut. Nothing synchronises on
//! these counters: no thread reads one to decide whether another thread's
//! WRITE is visible. A reader wants a number, and under contention the peak
//! can miss a spike that two threads produced between one's load and its
//! store. The interpreter runs one program on one thread, so that race is not
//! reachable here; if it ever is, the number becomes a lower bound and should
//! be labelled one.

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

pub struct Counting;

impl Counting {
    fn grew(by: usize) {
        let live = LIVE.fetch_add(by, Relaxed) + by;
        // fetch_max rather than load-compare-store: the compare is the race.
        PEAK.fetch_max(live, Relaxed);
    }
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(l) };
        if !p.is_null() {
            Self::grew(l.size());
        }
        p
    }

    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        LIVE.fetch_sub(l.size(), Relaxed);
        unsafe { System.dealloc(p, l) }
    }

    /// **REALLOC IS NOT ALLOC PLUS DEALLOC and the difference is the whole
    /// number.** A `Vec` that grows to n bytes reallocs its way up in
    /// doublings; counting each step as a fresh allocation without releasing
    /// the old one reports 2n. The peak that matters is the moment both blocks
    /// are live, which is what this records: up by the new size first, then
    /// down by the old.
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
        let q = unsafe { System.realloc(p, l, new) };
        if !q.is_null() {
            Self::grew(new);
            LIVE.fetch_sub(l.size(), Relaxed);
        }
        q
    }

    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc_zeroed(l) };
        if !p.is_null() {
            Self::grew(l.size());
        }
        p
    }
}

/// Bytes held right now, and the most ever held since the last `reset`.
pub fn live() -> usize {
    LIVE.load(Relaxed)
}

pub fn peak() -> usize {
    PEAK.load(Relaxed)
}

/// Drop the high-water mark to what is live NOW, so the next program is
/// measured on its own.
///
/// It resets to `live` and not to zero, because what is already held is real
/// and the next program's peak includes it -- the subject it is about to walk
/// is in that number. Resetting to zero would report a peak smaller than the
/// memory in use at the moment it was taken.
pub fn reset() {
    PEAK.store(LIVE.load(Relaxed), Relaxed);
}

/// Megabytes, for a column that has to line up.
pub fn mb(bytes: usize) -> f64 {
    bytes as f64 / (1024.0 * 1024.0)
}
