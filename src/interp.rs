//! A tree-walking interpreter over the desugared AST.
//!
//! **It has no type checker and does not need one.** A value knows what it is,
//! so `a + b` looks at the two values in hand; the checker's job is to prove
//! ahead of time that they will be the right ones. What this buys is an oracle
//! the type checker cannot be: a wrong SHAPE -- `a - b` for `b - a`, `+` and
//! `*` at the same precedence, `|>` with its operands the wrong way round --
//! is almost always well-typed, and shows up here as a wrong number.
//!
//! Where a declared type genuinely changes behaviour, it is READ, because a
//! declared type is syntax. `Score { v = 250 }` where the field is `Integer
//! between 0 and 100 clamping` evaluates to 100, and the bound comes from the
//! record's own definition. Inferred types are the ones we do not have.
//!
//! Anything unimplemented raises an error that NAMES it. A silent wrong answer
//! would make the whole exercise worthless.
//!
//! **What it walks is `Code`, not `Expr`** -- see `crate::code`. The chapter is
//! compiled once into a form where a local is a frame slot, a global is an
//! index, a literal is already a value and an application spine is already
//! flat, so nothing here resolves a name or parses a literal while the program
//! is running.

use crate::ast::*;
use crate::code::{Arm, Code, Compiler, Names, PatCode, Stmt};
use crate::symbol::{Sym, SymTab};
use std::collections::HashMap;
use std::fmt::Write as _;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub enum Value {
    Int(i64),
    Real(f64),
    Text(Rc<Str>),
    Char(char),
    Bool(bool),
    /// A LIST IS SHARED AND ITS SLOTS ARE WRITABLE, because Codex's is.
    ///
    /// `list-set-at` is an in-place mutator upstream and the compiler's skip
    /// list links its nodes by nothing else -- `splice-new-node` discards both
    /// results and returns the list it was given. A copying `list-set-at`
    /// leaves every insert structurally invisible while `size` still advances,
    /// which is how a 266-name scope ends up unsearchable and a function's own
    /// parameter comes back `CDX3002 Undefined name`.
    ///
    /// The wasm plug shipped the copy first and row 8 of `plugs-backlog.md`
    /// records the same symptom, so this is a transcribed defect and not a
    /// guess. `list-set-at` is the ONLY writer; `list-push`, `&` and `::` all
    /// allocate.
    List(Rc<RefCell<Vec<Value>>>),
    /// A record literal: its type name and its fields. A name is a four-byte
    /// `Sym`, so building a record copies nothing and this variant is the
    /// smallest thing that can carry two.
    /// A RECORD IS SHARED AND MUTABLE, because Codex's is.
    ///
    /// `st.offset = stop` is a field ASSIGNMENT and it writes through: the
    /// compiler's lexer ends `scan-ident-rest` with
    ///
    /// ```text
    /// in let __seq = st.offset = stop
    /// in let __seq = st.column = new-col
    /// in st
    /// ```
    ///
    /// and returns the same `st` it was handed, expecting the two assignments
    /// to be visible in it. This arm used to build a NEW record and return it,
    /// so the sequence threw the update away and the scanner re-read the same
    /// character forever -- `"x"` lexed in 692 steps and `"xy"` never finished.
    ///
    /// The alternative was to rebind the assigned NAME for the rest of the
    /// sequence, which is cheaper and covers all 49 sites in the checkout,
    /// every one of which assigns through a plain local. It was rejected
    /// because it cannot be made to FAIL LOUDLY when a second binding aliases
    /// the same record: at the moment of assignment the record is already held
    /// by the environment and by the evaluator, so a reference count cannot
    /// separate an innocent alias from a live one. An interpreter whose answer
    /// depends on how a program NAMES a value, silently, is worse than a slower
    /// one.
    ///
    /// `Rc<RefCell<..>>` is still one pointer, so `Value` stays 16 bytes -- the
    /// property that made `Rc<str>` cost 16% does not apply here.
    Record(Sym, Rc<RefCell<Vec<(Sym, Value)>>>),
    /// A variant constructor, saturated or not.
    Ctor(Sym, Rc<Vec<Value>>),
    Fun(Rc<Closure>),
    /// `Nothing` and friends -- a nullary name we do not otherwise know.
    Unit,
}

/// What a saturated closure RUNS.
///
/// A constructor and a builtin used to be encoded as a `NameRef` holding
/// `__ctor:`/`__builtin:` and the name -- which meant a `format!` on every
/// reference and a `to_string` on every call to take the prefix back off.
/// Naming the three cases allocates nothing.
#[derive(Clone, Debug)]
pub enum Body {
    /// A definition's or a lambda's compiled body.
    Code(Rc<Code>),
    /// A variant constructor: the arguments ARE the value.
    Ctor(Sym),
    /// A compiler builtin, resolved to its name once.
    Builtin(&'static str),
}

#[derive(Debug)]
pub struct Closure {
    /// **WHOSE BODY THIS IS**, which the run does not need and an instrument
    /// does. It is the only way to answer "where did the memory go" with a
    /// name instead of a number: the peak is sampled against whatever is
    /// executing, and without this every answer is "somewhere in the
    /// compiler". A `Sym` is four bytes on a heap-allocated Closure, so it
    /// costs nothing that shows up.
    pub name: Sym,
    /// How many arguments saturate it. The parameters have NAMES in the
    /// source and none here: `crate::code` turned every reference to one into
    /// a slot in this call's frame, so the run never asks what they were.
    pub arity: usize,
    pub body: Body,
    pub env: Env,
    pub applied: Vec<Value>,
}

/// A TEXT, AND WHERE IT LIVES.
///
/// The address is not decoration and it is not for debugging: the compiler
/// asks `address-of t < b` to decide whether a text is durable enough to share
/// or has to be rebuilt, and a raw host pointer cannot answer that question
/// against an allocator offset. It is stamped once, at the moment the text is
/// made, from the same cursor `__heap-save` reads -- so it is below every base
/// computed after it and at or above every one before, which is the whole of
/// what the test wants to know.
///
/// Behind the `Rc` rather than beside it in the variant, because `Value` is
/// two words and that is load-bearing: it was 24 bytes once and 16% slower.
#[derive(Debug)]
pub struct Str {
    pub addr: i64,
    s: String,
}

impl Str {
    pub fn as_str(&self) -> &str {
        &self.s
    }
}

/// **TWO TEXTS ARE EQUAL WHEN THEY READ THE SAME**, whatever their addresses.
/// Codex compares texts by content and always has; the address answers a
/// different question and `address-of` is where it is asked.
impl PartialEq for Str {
    fn eq(&self, other: &Str) -> bool {
        self.s == other.s
    }
}

impl std::ops::Deref for Str {
    type Target = str;
    fn deref(&self) -> &str {
        &self.s
    }
}

impl std::fmt::Display for Str {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.s)
    }
}

pub type Env = Rc<Scope>;

/// One frame: the values, positionally.
///
/// A call binds its whole parameter list at once; a `let` binding, an `act`
/// bind and a match arm's captures each get a frame of their own, in the order
/// the compiler counted them. A name never appears, so a lookup is `hops`
/// pointer hops and an index -- no comparison, no hashing, no allocation.
#[derive(Debug)]
pub struct Scope {
    vals: Vec<Value>,
    parent: Option<Env>,
}

impl Scope {
    fn root() -> Env {
        Rc::new(Scope { vals: Vec::new(), parent: None })
    }
    fn get(&self, hops: u32, slot: u32) -> Option<Value> {
        let mut here = self;
        for _ in 0..hops {
            here = here.parent.as_deref()?;
        }
        here.vals.get(slot as usize).cloned()
    }
    fn push(parent: &Env, vals: Vec<Value>) -> Env {
        Rc::new(Scope { vals, parent: Some(parent.clone()) })
    }
}

pub struct Error(pub String);

/// What evaluating an expression in TAIL POSITION produced.
///
/// **Codex has no loop construct: iteration IS tail recursion.**
/// `scan-ident-end source (offset + 1) len` recurses once per byte of the
/// source, so on the compiler's own 2.98 MB that is millions of frames deep.
/// Cobblestone's zig emitter turns a self-call into a `while (true)` for the
/// same reason. An interpreter that recurses per iteration needs a stack frame
/// per byte and cannot finish; one that LOOPS needs one.
enum Step {
    Done(Value),
    /// A saturated call to make next, in place of the one that just returned.
    Call(Rc<Closure>, Vec<Value>),
}

type R<T> = Result<T, Error>;

fn err<T>(msg: impl Into<String>) -> R<T> {
    Err(Error(msg.into()))
}

/// A FRESH list. Every construction goes through here, because a shared
/// backing that was meant to be new is the way `list-set-at`'s write-through
/// turns into a leak between two lists that were never the same one.
fn list(cells: Vec<Value>) -> Value {
    Value::List(Rc::new(RefCell::new(cells)))
}

/// Stamp a location on an error that does not have one. The innermost frame
/// wins, which is the one a reader wants.
fn at(e: Error, sp: Span) -> Error {
    if e.0.starts_with('L') {
        e
    } else {
        Error(format!("L{}C{}: {}", sp.line, sp.col, e.0))
    }
}

/// A record field whose declared type carries a bound, and what to do at it.
#[derive(Clone, Copy, Debug)]
pub struct FieldBound {
    pub lo: i64,
    pub hi: i64,
    pub mode: OverflowMode,
}

pub struct Interp {
    /// Every top-level function, constructor and builtin of one argument or
    /// more, as a ready value. `Code::Global` indexes this, so a reference is
    /// an index and a refcount.
    globals: Vec<Value>,
    /// The compiled bodies of the definitions that take NO parameters. A
    /// reference evaluates one; Codex is pure, so that is a cost and not a
    /// meaning.
    const_defs: Vec<Rc<Code>>,
    /// The value of each nullary that has already been forced, and whether it
    /// is one we are allowed to keep.
    ///
    /// **A nullary is re-evaluated at every mention, and that is a whole
    /// complexity class on the tables this compiler is pointed at.** Measured
    /// on safari's `build-world`: one mention costs about 350,000 steps, two
    /// cost 700,000, exactly linear. `pose-rest-polys` is 2,198 records rebuilt
    /// per mention. The game's own port notes record the same shape from the
    /// other side -- PORTING_NOTES B13, a nullary emits as a FUNCTION in zig
    /// and allocates per call, per frame.
    ///
    /// Codex bindings are pure, so forcing one twice can only cost. THE GUARD
    /// IS THE EFFECT ROW AND NOTHING ELSE: `opening : [Console] Nothing` is
    /// also a nullary, and an act performed once is not an act performed twice.
    /// A definition with no annotation at all is not cached either, because
    /// what is not declared is not known here -- the checker infers, this pass
    /// does not.
    ///
    /// This is a place the Rust arm deliberately does BETTER than the zig,
    /// rather than the same. The output is identical because the language is
    /// pure; only the work differs.
    const_cache: Vec<Option<Value>>,
    const_cacheable: Vec<bool>,
    /// Does this program contain a WRITER at all -- a `list-set-at`, a
    /// `__record-set`, or a field assignment? If it does not, nothing can
    /// reach into a cached value and every nullary may hand out one object.
    /// See `frozen`.
    writes: bool,
    /// `opening`, compiled in the empty environment.
    opening: Option<Rc<Code>>,
    /// `Type.field -> bound`, and the ONE thing resolution cannot do ahead of
    /// time. A record literal names its type, so its bounds are attached at
    /// compile time; a field ASSIGNMENT names only the field, and which record
    /// it lands on is whatever the left-hand side evaluates to.
    bounds: HashMap<(Sym, Sym), FieldBound>,
    /// Spells a name when one has to be printed: an error, or `show`.
    syms: SymTab,
    /// The empty environment, shared: every top-level closure closes over it.
    root: Env,
    /// Names defined in more than one chapter of a bundled unit.
    /// `drive-unit.codex` has two `bar-quad`s -- one over `ScreenPt` and one
    /// over `RiderPt` -- and keeping only the last silently gave the wrong one
    /// to every caller of the other. Reported, not used: resolving them is
    /// `crate::code`'s job and it happens before the run.
    pub collisions: Vec<String>,
    pub out: String,
    /// How much work the run did, which is the only speed number that is not
    /// about this machine on this day.
    pub steps: u64,
    depth: u32,
    limit: u64,
    /// THE ALLOCATOR'S BOOKKEEPING, AND NOTHING IS ALLOCATED.
    ///
    /// The compiler manages its own memory: a bump heap with a deck growing
    /// under it, `__heap-advance` to reserve, `__heap-restore` to give back,
    /// and `phase-compact` -- which is exactly `__heap-restore (__deck-pos)` --
    /// between phases. On bare metal and in the plugs that is real. Here the
    /// host allocator does the job, so these two counters carry the ARITHMETIC
    /// and none of the memory.
    ///
    /// They are not zero and they are not constant, because the compiler asks
    /// them questions. `deck-short-of ceiling band` is
    /// `__deck-pos + band >= ceiling`, and `heap-short-of` the same over
    /// `__heap-save`, so a position frozen at zero would answer those two the
    /// way a machine with no memory left does, or the way one with infinite
    /// memory does, depending on the ceiling -- and neither is the answer a
    /// real run gives. Moving them the way a bump allocator moves them is the
    /// cheapest model that gets those two predicates right.
    ///
    /// **WHAT THIS ARM THEREFORE CANNOT SEE.** Every defect the deck bracket
    /// has produced upstream -- a lifetime error, a value read after the
    /// bracket reclaimed it -- is invisible from here, because nothing here
    /// reclaims anything. Agreement between this arm and bare metal is
    /// evidence about the SEMANTICS and silence about the memory DISCIPLINE.
    /// Do not let a green line be read as covering both.
    ///
    /// The line is not where it looks, though, and `Mem` is the reason. The
    /// type checker's memo and cons tables are raw memory -- reserved off
    /// `__heap-save`, zeroed with `__memset`, probed with `peek-32` over
    /// `table + idx * 8` -- so the addresses these counters hand out are read
    /// back as data by the program under test. What is missing is reclamation,
    /// not addressing.
    /// The two cursors and the extent depth between them. `crate::bump` owns
    /// the arithmetic, and owns it separately so it can be tested without a
    /// program to run.
    bump: crate::bump::Bump,
    /// Each constructor's position in its own variant declaration, which is
    /// what `variant-tag` answers.
    tags: HashMap<Sym, i64>,
    /// THE FLAT MEMORY THE ALLOCATOR HANDS OUT ADDRESSES INTO.
    mem: Mem,
    /// WHAT WAS RUNNING WHEN THE MEMORY WAS HIGHEST.
    ///
    /// Sampled rather than exact, every `SAMPLE_STEPS` steps, because the
    /// allocator counter is a global and the interpreter cannot be called back
    /// from it. A peak reached and released entirely between two samples is
    /// missed; one that stands for even a fraction of a millisecond is not.
    /// The name is the innermost definition entered, which is the one worth
    /// having -- an allocation made three frames down is attributed to the
    /// frame that made it.
    /// Full-length `substring` calls and their bytes: what the keep phase
    /// rebuilt because nothing could be recognised as already durable.
    pub rematerialised: u64,
    pub rematerialised_bytes: u64,
    live_hwm: usize,
    hwm_in: Sym,
    cur: Sym,
    /// Set to have a long run report where it has got to. `moves` counts
    /// entries into a different definition than the last one, which is the
    /// signal that separates "slow" from "stuck": a run making progress moves
    /// between definitions constantly, and one going round a loop does not.
    pub progress: bool,
    started: Option<std::time::Instant>,
    next_report: f64,
    moves: u64,
    /// **THE SAMPLES, KEPT.** `cur` is already read every `SAMPLE_STEPS` for
    /// the memory attribution and was then thrown away, one per second
    /// surviving into the log. Keeping them is a `HashMap` insert on a
    /// sampling path that already exists, and it turns one sample a second
    /// into ten thousand -- which is the difference between reading a scrolling
    /// log by eye and having a profile.
    ///
    /// The allocation delta since the previous sample is attributed to the same
    /// definition, on the same reasoning a sampling profiler attributes time:
    /// wrong for any single sample, right in aggregate.
    prof: HashMap<Sym, (u64, u64)>,
    /// How many builtin calls, and how many frames pushed. Exact rather than
    /// sampled, because the sampler cannot see them: a builtin returns before
    /// the next sample is due, so `cur` is almost never inside one. Two
    /// increments on paths that already exist, and they answer the two
    /// questions an optimiser would otherwise guess at -- whether the string
    /// match over two hundred builtin arms is worth replacing with an index,
    /// and whether one `Rc<Scope>` per call is worth pooling.
    pub builtin_calls: u64,
    pub frames: u64,
    last_live: usize,
    /// Which chapter defines each name, so the profile can be bucketed by
    /// PHASE without anybody guessing from the name afterwards.
    home: HashMap<Sym, Rc<str>>,
}

/// One byte-addressed region starting at 0, sparse and paged.
///
/// **THE TYPE CHECKER IS A RAW-MEMORY PROGRAM and there is no interpreting it
/// without this.** `check-batch-open` reserves two hash tables off
/// `__heap-save`, zeroes them with `__memset`, and then `memo-probe-at` and
/// `cons-probe-at` walk them with `peek-32` and `peek-qword` over
/// `table + idx * 8`. Those are addresses, not handles: the memo layer
/// deduplicates types BY ADDRESS, so the identity the checker computes with is
/// the one this region defines.
///
/// Paged because the reservations are dense and the space between them is not:
/// the driver opens with `__heap-advance 536870912`, half a gigabyte nobody
/// writes a byte of. 4 KB pages, allocated on first WRITE -- a read of an
/// unmapped page answers zero and maps nothing, which is what `cx_buf_want`
/// growing a zeroed region does.
#[derive(Default)]
struct Mem {
    pages: HashMap<i64, Box<[u8; MEM_PAGE as usize]>>,
}

const MEM_PAGE: i64 = 4096;

impl Mem {
    fn byte(&self, addr: i64) -> u8 {
        self.pages
            .get(&addr.div_euclid(MEM_PAGE))
            .map_or(0, |p| p[addr.rem_euclid(MEM_PAGE) as usize])
    }

    fn set_byte(&mut self, addr: i64, v: u8) {
        let page = self
            .pages
            .entry(addr.div_euclid(MEM_PAGE))
            .or_insert_with(|| Box::new([0u8; MEM_PAGE as usize]));
        page[addr.rem_euclid(MEM_PAGE) as usize] = v;
    }

    /// A little-endian load of `width` bytes.
    ///
    /// The result is the bit pattern: at eight bytes that is a signed i64 and
    /// may be negative, and below eight it is zero-extended and cannot be.
    /// That split is not a choice made here -- `cx_peek_qword` rebuilds its
    /// value with WRAPPING arithmetic and says why in its own comment, while
    /// `cx_peek_32` uses checked arithmetic and cannot overflow; wasm emits
    /// `i64.load` against `i64.extend_i32_u`. Both plugs, the same split.
    fn load(&self, addr: i64, width: u32) -> i64 {
        // **ONE PAGE LOOKUP, NOT ONE PER BYTE.** A `peek-qword` was eight
        // hash lookups, and `cons-probe-at` -- the checker's cons table walking
        // its linear probe with fuel 64 -- does one per probe step. That loop
        // held 49 to 59 of every 60 samples for the last 458 seconds of a
        // self-compile. The straddling case is rare and still correct: nothing
        // aligns a memo slot to a page, so it has its own test.
        let page = addr.div_euclid(MEM_PAGE);
        let off = addr.rem_euclid(MEM_PAGE) as usize;
        let w = width as usize;
        let mut v: u64 = 0;
        if off + w <= MEM_PAGE as usize {
            match self.pages.get(&page) {
                None => return 0,
                Some(p) => {
                    for j in (0..w).rev() {
                        v = (v << 8) | p[off + j] as u64;
                    }
                }
            }
        } else {
            for j in (0..w as i64).rev() {
                v = (v << 8) | self.byte(addr + j) as u64;
            }
        }
        v as i64
    }

    /// How many bytes of pages this region has mapped, and the highest address
    /// ever written.
    ///
    /// **THE FLAT MEMORY IS NOT RECLAIMED AND THE ALLOCATOR MODEL DOES NOT
    /// KNOW THAT.** `__heap-restore` moves a counter back; the pages a program
    /// wrote before the restore stay mapped. On bare metal the same restore
    /// makes those bytes available again, so a checker that reserves a memo
    /// table per batch reuses ONE region there and accumulates regions here --
    /// if the reservations climb rather than repeat. Which of those is
    /// happening is a measurement, and this is the instrument for it.
    fn mapped(&self) -> usize {
        self.pages.len() * MEM_PAGE as usize
    }

    /// A little-endian store of the low `width` bytes, and no byte beyond.
    fn store(&mut self, addr: i64, width: u32, v: i64) {
        let bits = v as u64;
        let page = addr.div_euclid(MEM_PAGE);
        let off = addr.rem_euclid(MEM_PAGE) as usize;
        let w = width as usize;
        if off + w <= MEM_PAGE as usize {
            let p = self
                .pages
                .entry(page)
                .or_insert_with(|| Box::new([0u8; MEM_PAGE as usize]));
            for j in 0..w {
                p[off + j] = (bits >> (8 * j)) as u8;
            }
        } else {
            for j in 0..w as i64 {
                self.set_byte(addr + j, (bits >> (8 * j)) as u8);
            }
        }
    }

    /// Fill `n` bytes, a page at a time rather than a lookup at a time. The
    /// checker zeroes its cons table this way at every batch open, and those
    /// tables are megabytes.
    fn fill(&mut self, addr: i64, n: i64, v: u8) {
        let mut at = addr;
        let end = addr + n;
        while at < end {
            let page = at.div_euclid(MEM_PAGE);
            let off = at.rem_euclid(MEM_PAGE) as usize;
            let take = ((MEM_PAGE as usize - off) as i64).min(end - at) as usize;
            let p = self
                .pages
                .entry(page)
                .or_insert_with(|| Box::new([0u8; MEM_PAGE as usize]));
            p[off..off + take].fill(v);
            at += take as i64;
        }
    }
}

/// The default budget for ONE program: effectively none.
///
/// A step limit exists to bound a SWEEP, where one runaway program would
/// otherwise own the machine. Applying a sweep's budget to a single run makes
/// the tool refuse work it could do -- `ride-unit` simulates a whole ride and
/// legitimately needs hundreds of millions of steps.
const STEP_LIMIT: u64 = u64::MAX;
/// Codex recursion is unbounded and ours is a Rust call stack, so a runaway
/// program has to be caught by a counter rather than by the operating system:
/// a stack overflow aborts the process and takes the whole sweep with it.
const DEPTH_LIMIT: u32 = 20_000;

/// **HOW OFTEN A LONG RUN SAYS WHERE IT IS.** A compile that takes minutes and
/// prints nothing is indistinguishable from one that is stuck, and the
/// difference matters most exactly when the wait is longest. Every second,
/// checked on a step mask so the clock is read about ten times a second rather
/// than forty million.
const PROGRESS_STEPS: u64 = 1 << 22;

/// How often the memory high-water mark is attributed to a running definition.
/// A power of two, so the test is a mask rather than a division; 4,096 steps
/// is about a ten-thousandth of a second at the rate this runs.
const SAMPLE_STEPS: u64 = 4096;

impl Interp {
    /// Build the tables, then compile the chapter against them.
    ///
    /// **Every index is handed out before any body is compiled**, because a
    /// body may name a definition that comes after it -- so the globals vector
    /// is sized and filled in two passes rather than one.
    pub fn new(ch: &Chapter) -> Interp {
        let root = Scope::root();
        let mut names = Names::default();
        let mut globals: Vec<Value> = Vec::new();
        // Who defines each name. First definition wins, which is the same rule
        // the collision report uses; a name in two chapters is reported there
        // and is not this table's problem to solve.
        let mut home: HashMap<Sym, Rc<str>> = HashMap::new();
        for d in &ch.defs {
            home.entry(d.name).or_insert_with(|| Rc::from(d.chapter_slug.as_str()));
        }

        // Pass 1: an index for every definition, and who owns each name.
        let mut fun_defs: Vec<(u32, &Def)> = Vec::new();
        let mut const_defs_src: Vec<&Def> = Vec::new();
        let mut owners: HashMap<Sym, Vec<&str>> = HashMap::new();
        for d in &ch.defs {
            let slugs = owners.entry(d.name).or_default();
            if !slugs.contains(&d.chapter_slug.as_str()) {
                slugs.push(d.chapter_slug.as_str());
            }
            let key = (d.chapter_slug.clone(), d.name.clone());
            if d.params.is_empty() {
                let i = const_defs_src.len() as u32;
                const_defs_src.push(d);
                names.consts.insert(d.name, i);
                names.by_chapter_const.insert(key, i);
            } else {
                let i = globals.len() as u32;
                globals.push(Value::Unit);
                fun_defs.push((i, d));
                names.funs.insert(d.name, i);
                names.by_chapter_fun.insert(key, i);
            }
        }
        let mut collisions: Vec<String> = owners
            .iter()
            .filter(|(_, s)| s.len() > 1)
            .map(|(n, _)| ch.syms.text(*n).to_string())
            .collect();
        collisions.sort();
        names.colliding =
            owners.iter().filter(|(_, s)| s.len() > 1).map(|(n, _)| *n).collect();

        // Record field bounds, and a slot for every constructor.
        let mut ctors: Vec<(u32, Sym, usize)> = Vec::new();
        let mut tags: HashMap<Sym, i64> = HashMap::new();
        for t in &ch.type_defs {
            match t {
                TypeDef::Record(name, _, fields, ..) => {
                    for f in fields {
                        if let TypeExpr::BoundedInt(_, lo, hi, mode, _) = &f.type_expr {
                            names.bounds.insert(
                                (*name, f.name),
                                FieldBound { lo: *lo, hi: *hi, mode: *mode },
                            );
                        }
                    }
                }
                TypeDef::Variant(_, _, cs, _) => {
                    for (tag, c) in cs.iter().enumerate() {
                        let i = globals.len() as u32;
                        globals.push(Value::Unit);
                        names.ctors.insert(c.name, i);
                        // THE TAG IS THE CONSTRUCTOR'S POSITION IN ITS OWN
                        // DECLARATION, which is what `variant-tag` answers and
                        // what the unifier compares. It is only correct if this
                        // walk keeps the declared order, so it reads the order
                        // rather than sorting or hashing.
                        tags.insert(c.name, tag as i64);
                        ctors.push((i, c.name, c.fields.len()));
                    }
                }
                TypeDef::Unit(..) => {}
            }
        }

        // The arity comes from the compiler's own table, not from a list here:
        // a builtin applied to the wrong number of arguments would otherwise be
        // a silent partial application rather than a call.
        //
        // **`Some(0)` IS NOT `None` AND NEITHER IS ONE.** Both used to be read
        // as "declares no type" and given an arity of one, so `get-ticks :
        // Integer` -- a value -- became a function of one argument, and a
        // reference to it bound a `Fun` where an Integer belonged. Nothing
        // failed there: it failed fifteen lines away, in `keys-collision`, as
        // ``builtin `bit-and` is not interpreted yet (given a function, an
        // integer)`` -- a wrong-arity bug wearing a missing-feature message.
        for (name, arity) in crate::builtins::BUILTINS {
            match arity {
                None => {
                    if let Some(s) = ch.syms.find(name) {
                        names.builtin_undeclared.insert(s, name);
                    }
                }
                Some(0) => {
                    if let Some(s) = ch.syms.find(name) {
                        names.builtin_nullary.insert(s, name);
                    }
                }
                Some(arity) => {
                    // A builtin the chapter never names cannot be what any
                    // symbol here means, so it needs no slot.
                    let Some(sym) = ch.syms.find(name) else { continue };
                    let i = globals.len() as u32;
                    globals.push(Value::Fun(Rc::new(Closure {
                        name: sym,
                        arity,
                        body: Body::Builtin(name),
                        env: root.clone(),
                        applied: Vec::new(),
                    })));
                    names.builtin_funs.insert(sym, i);
                }
            }
        }

        // Constructors are FIXED for the run, so their values are built here
        // and every reference clones one refcount.
        for (i, name, arity) in ctors {
            let rc = name;
            globals[i as usize] = if arity == 0 {
                Value::Ctor(rc, Rc::new(Vec::new()))
            } else {
                Value::Fun(Rc::new(Closure {
                    name: rc,
                    arity,
                    body: Body::Ctor(rc),
                    env: root.clone(),
                    applied: Vec::new(),
                }))
            };
        }

        // Pass 2: compile. The tables are complete, so a body can name
        // anything the unit defines regardless of where it sits.
        let impure = impure_names(&ch.syms, &const_defs_src, &fun_defs);
        let writes = program_writes(&ch.syms, &const_defs_src, &fun_defs);
        let mut const_defs: Vec<Rc<Code>> = Vec::with_capacity(const_defs_src.len());
        let mut const_cacheable: Vec<bool> = Vec::with_capacity(const_defs_src.len());
        for d in &const_defs_src {
            const_defs.push(Rc::new(Compiler::body(&names, &ch.syms, &d.chapter_slug, &d.body)));
            const_cacheable.push(match d.declared_type.first() {
                Some(t) => !mentions_effect(t) && !impure.contains(&d.name),
                None => false,
            });
        }
        for (i, d) in &fun_defs {
            globals[*i as usize] = Value::Fun(Rc::new(Closure {
                name: d.name,
                arity: d.params.len(),
                body: Body::Code(Rc::new(Compiler::def(&names, &ch.syms, d))),
                env: root.clone(),
                applied: Vec::new(),
            }));
        }
        // The entry point runs in the EMPTY environment, whatever it declares,
        // which is what the walker did. Last definition of the name wins, as
        // it does everywhere else.
        let opening = ch
            .defs
            .iter()
            .rev()
            .find(|d| Some(d.name) == ch.syms.find("opening"))
            .map(|d| Rc::new(Compiler::body(&names, &ch.syms, &d.chapter_slug, &d.body)));

        Interp {
            globals,
            const_cache: vec![None; const_defs.len()],
            const_cacheable,
            writes,
            const_defs,
            opening,
            bounds: names.bounds,
            syms: ch.syms.clone(),
            root,
            collisions,
            out: String::new(),
            steps: 0,
            depth: 0,
            limit: STEP_LIMIT,
            bump: crate::bump::Bump::default(),
            tags,
            mem: Mem::default(),
            rematerialised: 0,
            rematerialised_bytes: 0,
            live_hwm: 0,
            hwm_in: Sym::default(),
            cur: Sym::default(),
            progress: false,
            started: None,
            next_report: 1.0,
            moves: 0,
            prof: HashMap::new(),
            builtin_calls: 0,
            frames: 0,
            last_live: 0,
            home,
        }
    }

    /// Bound this run to a number of steps. The sweep sets one; a single run
    /// does not.
    pub fn with_budget(mut self, steps: u64) -> Self {
        self.limit = steps;
        self
    }

    /// Run `opening`, the entry point every Codex program has.
    pub fn run(&mut self) -> R<()> {
        let Some(open) = self.opening.clone() else {
            return err("no `opening` definition to run");
        };
        let env = self.root.clone();
        self.eval(&open, &env)?;
        Ok(())
    }

    fn eval(&mut self, c: &Code, env: &Env) -> R<Value> {
        self.steps += 1;
        if self.steps > self.limit {
            return err("step limit reached; the program did not finish");
        }
        if self.steps & (SAMPLE_STEPS - 1) == 0 {
            let live = crate::heapwatch::live();
            if live > self.live_hwm {
                self.live_hwm = live;
                self.hwm_in = self.cur;
            }
            if self.progress {
                let e = self.prof.entry(self.cur).or_insert((0, 0));
                e.0 += 1;
                e.1 += live.saturating_sub(self.last_live) as u64;
                self.last_live = live;
            }
        }
        if self.progress && self.steps & (PROGRESS_STEPS - 1) == 0 {
            self.report_progress();
        }
        self.depth += 1;
        if self.depth > DEPTH_LIMIT {
            self.depth -= 1;
            return err("recursion limit reached");
        }
        let r = self.eval_inner(c, env);
        self.depth -= 1;
        r
    }

    fn eval_inner(&mut self, c: &Code, env: &Env) -> R<Value> {
        match c {
            Code::Const(v) => Ok(v.clone()),
            Code::Local(hops, slot) => env
                .get(*hops, *slot)
                .ok_or_else(|| Error(format!("internal: no local at ({hops}, {slot})"))),
            Code::Global(i) => Ok(self.globals[*i as usize].clone()),
            Code::ConstDef(i) => {
                let i = *i as usize;
                if let Some(v) = &self.const_cache[i] {
                    return Ok(v.clone());
                }
                let body = self.const_defs[i].clone();
                let root = self.root.clone();
                let v = self.eval(&body, &root)?;
                // Only after it returns: a self-referential nullary must still
                // recurse to its own error rather than see a half-built answer.
                if self.const_cacheable[i] && (!self.writes || frozen(&v)) {
                    self.const_cache[i] = Some(v.clone());
                }
                Ok(v)
            }
            Code::NullaryBuiltin(name) => self.builtin(name, Vec::new()),
            Code::Fail(msg) => Err(Error(msg.clone())),
            Code::Unsupported(msg) => err(*msg),
            Code::Apply(head, args) => match self.apply_spine(head, args, env, false)? {
                Step::Done(v) => Ok(v),
                Step::Call(c, applied) => self.call(c, applied),
            },
            Code::Binary(l, op, r) => {
                // `and` and `or` SHORT-CIRCUIT, and programs depend on it for
                // safety rather than speed:
                //
                //   list-length c.segs > 0 and list-at c.segs (... - 1) == s
                //
                // evaluates `list-at` on an empty list if the right operand is
                // taken eagerly. `&` is short-circuited too when its left is a
                // boolean -- for text, lists and integers it is not a
                // conjunction at all, and the left says which.
                let a = self.eval(l, env)?;
                match (op, &a) {
                    (BinaryOp::OpBoolAnd | BinaryOp::OpAnd, Value::Bool(false)) => {
                        return Ok(Value::Bool(false))
                    }
                    (BinaryOp::OpOr, Value::Bool(true)) => return Ok(Value::Bool(true)),
                    _ => {}
                }
                let b = self.eval(r, env)?;
                {
                    let Interp { syms, bump, .. } = self;
                    binary(syms, bump, *op, a, b)
                }
            }
            Code::Unary(x) => match self.eval(x, env)? {
                Value::Int(i) => Ok(Value::Int(-i)),
                Value::Real(f) => Ok(Value::Real(-f)),
                v => err(format!("negation of {}", type_name(&v))),
            },
            Code::If(c, t, f) => match self.eval(c, env)? {
                Value::Bool(true) => self.eval(t, env),
                Value::Bool(false) => self.eval(f, env),
                v => err(format!("`if` on {}", type_name(&v))),
            },
            Code::Let(vals, body) => {
                let mut env = env.clone();
                for v in vals {
                    let v = self.eval(v, &env)?;
                    env = Scope::push(&env, vec![v]);
                }
                self.eval(body, &env)
            }
            // The body is already shared: a lambda evaluated a million times
            // bumps a refcount rather than copying its tree.
            Code::Lambda(l) => Ok(Value::Fun(Rc::new(Closure {
                // A lambda has no name of its own; it is attributed to
                // whatever definition it was written inside.
                name: self.cur,
                arity: l.arity,
                body: Body::Code(l.body.clone()),
                env: env.clone(),
                applied: Vec::new(),
            }))),
            Code::Match(scrut, arms) => {
                let v = self.eval(scrut, env)?;
                self.match_arms(&v, arms, env)
            }
            Code::List(xs) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs {
                    out.push(self.eval(x, env)?);
                }
                Ok(list(out))
            }
            Code::Record(name, fields) => {
                let mut out = Vec::with_capacity(fields.len());
                for f in fields {
                    let mut v = self.eval(&f.value, env)?;
                    // The declared bound is syntax, so it is applied here.
                    if let (Value::Int(i), Some(b)) = (&v, &f.bound) {
                        v = Value::Int(apply_bound(*i, b));
                    }
                    out.push((f.name.clone(), v));
                }
                Ok(Value::Record(name.clone(), Rc::new(RefCell::new(out))))
            }
            Code::FieldAccess(obj, field, sp) => match self.eval(obj, env)? {
                Value::Record(name, fs) => fs
                    .borrow()
                    .iter()
                    .find(|(n, _)| n == field)
                    .map(|(_, v)| v.clone())
                    .ok_or_else(|| {
                        Error(format!(
                            "L{}C{}: `{}` has no field `{}` (it has {})",
                            sp.line,
                            sp.col,
                            self.syms.text(name),
                            self.syms.text(*field),
                            fs.borrow()
                                .iter()
                                .map(|(n, _)| self.syms.text(*n))
                                .collect::<Vec<_>>()
                                .join(", ")
                        ))
                    }),
                v => err(format!(
                    "L{}C{}: field `{}` read from {}",
                    sp.line,
                    sp.col,
                    self.syms.text(*field),
                    type_name(&v)
                )),
            },
            Code::Act(stmts) => {
                let mut env = env.clone();
                let mut last = Value::Unit;
                for s in stmts {
                    match s {
                        Stmt::Exec(e) => last = self.eval(e, &env)?,
                        Stmt::Bind(e) => {
                            let v = self.eval(e, &env)?;
                            env = Scope::push(&env, vec![v]);
                            last = Value::Unit;
                        }
                    }
                }
                Ok(last)
            }
            Code::Lazy(inner) => self.eval(inner, env),
            Code::DeckRecord(body) => {
                self.bump.enter();
                let v = self.eval(body, env);
                self.bump.exit();
                v
            }
            Code::FieldAssign(rec, field, val) => {
                let base = self.eval(rec, env)?;
                let v = self.eval(val, env)?;
                match base {
                    Value::Record(name, fs) => {
                        let bound = self.bounds.get(&(name, *field));
                        let v = match (&v, bound) {
                            (Value::Int(i), Some(b)) => Value::Int(apply_bound(*i, b)),
                            _ => v,
                        };
                        {
                            // The borrow is scoped so that nothing re-enters
                            // the evaluator while it is held -- `v` is already
                            // a value and the bound is already applied.
                            let mut out = fs.borrow_mut();
                            match out.iter_mut().find(|(n, _)| n == field) {
                                Some(slot) => slot.1 = v,
                                None => out.push((*field, v)),
                            }
                        }
                        // THE SAME RECORD, not a copy of it. Every other
                        // binding that reaches this one sees the assignment,
                        // which is what the compiler's `in ... in st` relies on.
                        Ok(Value::Record(name, fs))
                    }
                    v => err(format!("field assignment on {}", type_name(&v))),
                }
            }
        }
    }

    /// Run a saturated closure, looping on every tail call rather than
    /// recursing. Non-tail calls still nest, which is what a call stack is
    /// for; this is only about the ones that do not need to.
    fn call(&mut self, mut c: Rc<Closure>, mut applied: Vec<Value>) -> R<Value> {
        // The caller is restored on the way out, so `cur` names the frame that
        // is running rather than the deepest one ever entered.
        let caller = self.cur;
        let r = self.call_frames(&mut c, &mut applied);
        self.cur = caller;
        r
    }

    fn call_frames(&mut self, cell: &mut Rc<Closure>, args: &mut Vec<Value>) -> R<Value> {
        loop {
            let c = cell.clone();
            let applied = std::mem::take(args);
            if self.cur != c.name {
                self.moves += 1;
                self.cur = c.name;
            }
            let body = match &c.body {
                Body::Ctor(name) => return Ok(Value::Ctor(name.clone(), Rc::new(applied))),
                Body::Builtin(name) => {
                    let name = *name;
                    return self.builtin(name, applied);
                }
                Body::Code(b) => b.clone(),
            };
            self.frames += 1;
            let env = Scope::push(&c.env, applied);
            match self.eval_tail(&body, &env)? {
                Step::Done(v) => return Ok(v),
                Step::Call(next, next_args) => {
                    *cell = next;
                    *args = next_args;
                }
            }
        }
    }

    /// Evaluate, but hand a tail call BACK instead of making it.
    ///
    /// The tail positions are the ones that cannot do any work after the call
    /// returns: both branches of an `if`, the body of a `let`, an arm's body,
    /// and the last statement of an `act`.
    fn eval_tail(&mut self, c: &Code, env: &Env) -> R<Step> {
        self.steps += 1;
        if self.steps > self.limit {
            return err("step limit reached; the program did not finish");
        }
        match c {
            Code::If(c, t, f) => match self.eval(c, env)? {
                Value::Bool(true) => self.eval_tail(t, env),
                Value::Bool(false) => self.eval_tail(f, env),
                v => err(format!("`if` on {}", type_name(&v))),
            },
            Code::Let(vals, body) => {
                let mut env = env.clone();
                for v in vals {
                    let v = self.eval(v, &env)?;
                    env = Scope::push(&env, vec![v]);
                }
                self.eval_tail(body, &env)
            }
            Code::Match(scrut, arms) => {
                let v = self.eval(scrut, env)?;
                for a in arms.iter() {
                    let mut vals = Vec::with_capacity(a.nvars);
                    if !matches_pat(&v, &a.pat, &mut vals) {
                        continue;
                    }
                    let arm_env = Scope::push(env, vals);
                    if let Value::Bool(false) = self.eval(&a.guard, &arm_env)? {
                        continue;
                    }
                    return self.eval_tail(&a.body, &arm_env);
                }
                err("no match arm applied")
            }
            Code::Act(stmts) => {
                let mut env = env.clone();
                for (i, s) in stmts.iter().enumerate() {
                    let last = i + 1 == stmts.len();
                    match s {
                        Stmt::Exec(e) if last => return self.eval_tail(e, &env),
                        Stmt::Exec(e) => {
                            self.eval(e, &env)?;
                        }
                        Stmt::Bind(e) => {
                            let v = self.eval(e, &env)?;
                            env = Scope::push(&env, vec![v]);
                        }
                    }
                }
                Ok(Step::Done(Value::Unit))
            }
            Code::Apply(head, args) => self.apply_spine(head, args, env, true),
            _ => Ok(Step::Done(self.eval(c, env)?)),
        }
    }

    /// Apply a whole spine, gathering the arguments for one call instead of
    /// building a closure per argument.
    ///
    /// **Application is curried -- `f a b c` is three nested `Apply` nodes --
    /// but the call is not.** Taking them one at a time allocated an
    /// intermediate closure, its argument vector and a clone of every argument
    /// already applied, per argument: `map-list-loop` has five parameters, so
    /// every one of its calls built four closures it then threw away. The
    /// spine itself is flattened by `crate::code`, once, rather than re-walked
    /// into a fresh `Vec` on every application.
    ///
    /// **The ORDER is unchanged, and that is the whole constraint.** Arguments
    /// are still evaluated left to right, and a call that saturates PART WAY
    /// down the spine still runs before the arguments after it are evaluated
    /// -- `f a b` where `f` takes one argument runs `f a` before `b`.
    ///
    /// `tail` says whether the caller can loop on the last call rather than
    /// nesting; only `eval_tail` can.
    fn apply_spine(
        &mut self,
        head: &Code,
        args: &[(Code, Span)],
        env: &Env,
        tail: bool,
    ) -> R<Step> {
        // The nodes are still there and still evaluated; only the closures in
        // between are gone. Counting them keeps `steps` a measure of the
        // PROGRAM's work rather than of this interpreter's shape, so a rate
        // before this change and one after it are the same number.
        self.steps += args.len() as u64 - 1;
        let mut f = self.eval(head, env)?;
        let mut i = 0;
        while i < args.len() {
            let fun = match &f {
                Value::Fun(c) => Some(c.clone()),
                _ => None,
            };
            let Some(c) = fun.filter(|c| c.arity > c.applied.len()) else {
                // A constructor takes its fields one at a time, and anything
                // else is an error the one-argument path words properly.
                let (a, sp) = &args[i];
                let arg = self.eval(a, env)?;
                f = self.apply(f, arg).map_err(|e| at(e, *sp))?;
                i += 1;
                continue;
            };
            let take = (c.arity - c.applied.len()).min(args.len() - i);
            let mut applied = Vec::with_capacity(c.arity);
            applied.extend_from_slice(&c.applied);
            let sp = args[i + take - 1].1;
            for (a, _) in &args[i..i + take] {
                applied.push(self.eval(a, env)?);
            }
            i += take;
            if applied.len() < c.arity {
                f = Value::Fun(Rc::new(Closure {
                    name: c.name,
                    arity: c.arity,
                    body: c.body.clone(),
                    env: c.env.clone(),
                    applied,
                }));
            } else if tail && i == args.len() {
                return Ok(Step::Call(c, applied));
            } else {
                f = self.call(c, applied).map_err(|e| at(e, sp))?;
            }
        }
        Ok(Step::Done(f))
    }

    /// Apply one argument. A saturated closure comes back as a pending call so
    /// the caller can loop on it; everything else is finished here.
    fn apply_step(&mut self, f: Value, arg: Value) -> R<Step> {
        if let Value::Ctor(n, fields) = &f {
            let mut out = (**fields).clone();
            out.push(arg);
            return Ok(Step::Done(Value::Ctor(n.clone(), Rc::new(out))));
        }
        let Value::Fun(c) = f else {
            return err(format!("applied {} to an argument", type_name(&f)));
        };
        let mut applied = c.applied.clone();
        applied.push(arg);
        if applied.len() < c.arity {
            return Ok(Step::Done(Value::Fun(Rc::new(Closure {
                name: c.name,
                arity: c.arity,
                body: c.body.clone(),
                env: c.env.clone(),
                applied,
            }))));
        }
        Ok(Step::Call(c, applied))
    }

    fn apply(&mut self, f: Value, arg: Value) -> R<Value> {
        match self.apply_step(f, arg)? {
            Step::Done(v) => Ok(v),
            Step::Call(c, applied) => self.call(c, applied),
        }
    }

    fn match_arms(&mut self, v: &Value, arms: &[Arm], env: &Env) -> R<Value> {
        for a in arms {
            let mut vals = Vec::with_capacity(a.nvars);
            if !matches_pat(v, &a.pat, &mut vals) {
                continue;
            }
            let env = Scope::push(env, vals);
            match self.eval(&a.guard, &env)? {
                Value::Bool(false) => continue,
                _ => return self.eval(&a.body, &env),
            }
        }
        err("no match arm applied")
    }

    /// Where the next allocation goes: the deck while an extent is open, the
    /// bivy otherwise. One cursor with two homes, which is R10 on the metal.
    fn cursor(&self) -> i64 {
        self.bump.cursor()
    }

    fn set_cursor(&mut self, v: i64) {
        self.bump.set_cursor(v);
    }

    /// **THE PROFILE, BY CHAPTER AND BY DEFINITION.**
    ///
    /// Written out rather than returned, because both self-compile attempts so
    /// far were KILLED and a profile that only exists at exit is a profile
    /// nobody gets. This goes to stderr beside the progress lines, so the last
    /// dump before an interrupt is the answer.
    ///
    /// Chapters first: that is the phase breakdown, and the interpreter knows
    /// which chapter defines each name, so nobody has to infer it from the
    /// name afterwards.
    pub fn profile(&self, top: usize) -> String {
        let total: u64 = self.prof.values().map(|(n, _)| n).sum();
        if total == 0 {
            return String::new();
        }
        let mut out = format!(
            "\n--- profile: {total} samples, {} steps, {} builtin calls ({:.0}% of steps), {} frames\n",
            self.steps,
            self.builtin_calls,
            100.0 * self.builtin_calls as f64 / self.steps.max(1) as f64,
            self.frames,
        );
        let mut by_chapter: HashMap<&str, (u64, u64)> = HashMap::new();
        for (sym, (n, bytes)) in &self.prof {
            let ch = self.home.get(sym).map(|c| &**c).unwrap_or("(builtin or lambda)");
            let e = by_chapter.entry(ch).or_insert((0, 0));
            e.0 += n;
            e.1 += bytes;
        }
        let mut rows: Vec<_> = by_chapter.into_iter().collect();
        rows.sort_by_key(|(_, (n, _))| std::cmp::Reverse(*n));
        for (ch, (n, bytes)) in rows.iter().take(top) {
            out += &format!(
                "  {:5.1}%  {:>10} allocated  {}\n",
                100.0 * *n as f64 / total as f64,
                format!("{:.0} MB", crate::heapwatch::mb(*bytes as usize)),
                ch
            );
        }
        out += "  --- by definition\n";
        let mut defs: Vec<_> = self.prof.iter().collect();
        defs.sort_by_key(|(_, (n, _))| std::cmp::Reverse(*n));
        for (sym, (n, _)) in defs.iter().take(top) {
            out += &format!(
                "  {:5.1}%  {}\n",
                100.0 * *n as f64 / total as f64,
                self.syms.text(**sym)
            );
        }
        out
    }

    /// Say where this run has got to, at most once a second.
    ///
    /// To stderr, because stdout is the program's own output and a caller is
    /// diffing it. `moves` is cumulative rather than per-report so two lines
    /// can be subtracted; a run whose `moves` stops rising while `steps` keeps
    /// rising is going round something.
    fn report_progress(&mut self) {
        let t0 = *self.started.get_or_insert_with(std::time::Instant::now);
        let secs = t0.elapsed().as_secs_f64();
        if secs < self.next_report {
            return;
        }
        self.next_report = secs.floor() + 1.0;
        // Every thirty seconds the whole profile, so an interrupted run still
        // leaves one behind.
        if secs as u64 % 30 == 0 {
            eprint!("{}", self.profile(12));
        }
        eprintln!(
            "progress secs={secs:.0} steps={} live-mb={:.0} depth={} moves={} in={}",
            self.steps,
            crate::heapwatch::mb(crate::heapwatch::live()),
            self.depth,
            self.moves,
            self.syms.text(self.cur),
        );
    }

    /// Bytes of flat memory mapped, the furthest the allocator's cursor ever
    /// got, and the definition that was running when the most was held.
    pub fn memory(&self) -> (usize, i64, String) {
        (self.mem.mapped(), self.bump.hwm, self.syms.text(self.hwm_in).to_string())
    }

    /// **MAKING A TEXT ALLOCATES**, which is the whole change: the address is
    /// stamped from the same cursor `__heap-save` reads, so a text made before
    /// a base is below it and one made after is not.
    ///
    /// The size is the byte length, word-aligned, which is what a text
    /// occupies upstream -- `cx_concat` allocates `b.len` and bare metal bumps
    /// r10 by the same.
    fn text(&mut self, s: String) -> R<Value> {
        let addr = self.bump.alloc(s.len() as i64);
        Ok(Value::Text(Rc::new(Str { addr, s })))
    }

    fn builtin(&mut self, name: &str, args: Vec<Value>) -> R<Value> {
        use Value::*;
        self.builtin_calls += 1;

        match (name, args.as_slice()) {
            // -- console ------------------------------------------------------
            ("print-line-uni" | "print-line", [v]) => {
                // Spelled BEFORE the write: `show` reads the table and the
                // write takes the output buffer, and they are the same `self`.
                let line = show(&self.syms, v);
                let _ = writeln!(self.out, "{line}");
                Ok(Unit)
            }
            ("print-uni" | "print", [v]) => {
                let part = show(&self.syms, v);
                let _ = write!(self.out, "{part}");
                Ok(Unit)
            }

            // -- text ---------------------------------------------------------
            ("show" | "integer-to-text", [v]) => {
                let t = show(&self.syms, v);
                self.text(t)
            }
            ("text-length", [Text(t)]) => Ok(Int(t.len() as i64)),
            ("char-at", [Text(t), Int(i)]) => t
                .as_bytes()
                .get(*i as usize)
                .map(|b| Char(*b as char))
                .ok_or_else(|| Error(format!("char-at {i} past the end"))),
            // `char-code-at` indexes BYTES, and `char-code` is the private
            // frequency alphabet -- not ASCII. `char-code 'A'` is 41.
            ("char-code-at", [Text(t), Int(i)]) => Ok(Int(t
                .as_bytes()
                .get(*i as usize)
                .map(|b| char_code(*b))
                .unwrap_or(0))),
            ("char-code", [Char(c)]) => Ok(Int(char_code(*c as u8))),
            ("code-to-char", [Int(c)]) => Ok(Char(code_to_char(*c))),
            ("char-to-text" | "char-encode", [Char(c)]) => {
                let t = c.to_string();
                self.text(t)
            }
            ("substring", [Text(t), Int(start), Int(len)]) => {
                let b = t.as_bytes();
                let s = (*start).clamp(0, b.len() as i64) as usize;
                let e = (s + (*len).max(0) as usize).min(b.len());
                // **A FULL-LENGTH SUBSTRING IS NOT A SUBSTRING, IT IS A COPY.**
                // `substring t 0 (text-length t)` is the compiler's idiom for
                // rematerialising a text it has decided is not durable --
                // `copy-sx-text` and `mcopy-text-content` are both written that
                // way. Counting exactly that shape measures the bytes this arm
                // copies BECAUSE its durability test cannot answer, and no
                // ordinary substring is caught by it.
                if s == 0 && e == b.len() {
                    self.rematerialised += 1;
                    self.rematerialised_bytes += e as u64;
                }
                let t = String::from_utf8_lossy(&b[s..e]).into_owned();
                self.text(t)
            }
            ("text-contains", [Text(a), Text(b)]) => Ok(Bool(a.contains(b.as_str()))),
            ("text-starts-with", [Text(a), Text(b)]) => Ok(Bool(a.starts_with(b.as_str()))),
            ("text-ends-with", [Text(a), Text(b)]) => Ok(Bool(a.ends_with(b.as_str()))),
            ("text-replace", [Text(a), Text(b), Text(c)]) => {
                let r = a.replace(b.as_str(), c.as_str());
                self.text(r)
            }
            ("text-to-integer", [Text(t)]) => Ok(Int(t.trim().parse().unwrap_or(0))),
            // `text-compare` is over CCE bytes, which is char-code order and
            // not ASCII order.
            ("text-compare", [Text(a), Text(b)]) => {
                let (x, y) = (crate::preamble::cce_key(a), crate::preamble::cce_key(b));
                Ok(Int(match x.cmp(&y) {
                    std::cmp::Ordering::Less => -1,
                    std::cmp::Ordering::Equal => 0,
                    std::cmp::Ordering::Greater => 1,
                }))
            }
            // THESE THREE ARE RANGES ON THE CHAR-CODE, not Unicode classes,
            // and the emitter is the oracle for them. Each is a `sub`, a `cmp`
            // and a `setbe` -- an UNSIGNED window on the frequency alphabet:
            //
            //   is-whitespace   (c - 1)  <= 1   ->  1..=2    newline, space
            //   is-digit        (c - 3)  <= 9   ->  3..=12   the ten digits
            //   is-letter       (c - 13) <= 51  ->  13..=64  lower then upper
            //                or (c - 97) <= 30  ->  97..=127 the extended band
            //
            // Rust's `is_alphabetic` and `is_ascii_digit` agree on ASCII, but
            // only because the alphabet was built that way -- they agree by
            // coincidence and disagree above it. `is-whitespace` is the one
            // that shows it: a tab and a carriage return are NOT whitespace
            // here, because the alphabet gives them no code at all.
            ("is-letter", [Char(c)]) => {
                let k = char_code(*c as u8);
                Ok(Bool((13..=64).contains(&k) || (97..=127).contains(&k)))
            }
            ("is-digit", [Char(c)]) => Ok(Bool((3..=12).contains(&char_code(*c as u8)))),
            ("is-whitespace", [Char(c)]) => {
                Ok(Bool((1..=2).contains(&char_code(*c as u8))))
            }
            // `List Integer -> Text`, the bytes as written.
            ("raw-bytes-to-text", [List(xs)]) => {
                let bytes: Vec<u8> =
                    xs.borrow().iter().map(|v| if let Int(i) = v { *i as u8 } else { 0 }).collect();
                let t = String::from_utf8_lossy(&bytes).into_owned();
                self.text(t)
            }

            // -- lists --------------------------------------------------------
            ("list-length", [List(xs)]) => Ok(Int(xs.borrow().len() as i64)),
            ("list-at", [List(xs), Int(i)]) => (*i >= 0)
                .then(|| xs.borrow().get(*i as usize).cloned())
                .flatten()
                .ok_or_else(|| {
                    Error(format!("list-at {i} of a {}-element list", xs.borrow().len()))
                }),
            // `list-snoc` and `list-push` are ONE operation: the zig emitter
            // gives both the same `cx_ll_push(l, v)`, an append at the end.
            //
            // **AND IT APPENDS IN PLACE.** `cx_ll_push` is
            // `l.items.append(gpa, v); return l;` -- always the same handle,
            // never a copy. The compiler depends on it:
            // `tail-resolve-binding-chunk` fills a `__list-with-capacity`
            // chunk, DISCARDS every push's result, answers only a count, and
            // its caller then reads `chunk` positions 0..n. A copying push
            // hands that caller an empty list and `list-at 0` of it.
            ("list-push" | "list-snoc", [List(xs), v]) => {
                xs.borrow_mut().push(v.clone());
                Ok(List(xs.clone()))
            }
            // `cx_ll_insert_at` is `l.items.insert(gpa, i, v); return l;`, so
            // this writes through for the same reason `list-push` does.
            ("list-insert-at", [List(xs), Int(i), v]) => {
                let mut out = xs.borrow_mut();
                let i = *i;
                if i < 0 || i as usize > out.len() {
                    return err(format!("list-insert-at {i} of a {}-element list", out.len()));
                }
                out.insert(i as usize, v.clone());
                drop(out);
                Ok(List(xs.clone()))
            }
            // The capacity is an allocation hint upstream -- `cx_ll_empty` then
            // `ensureTotalCapacityPrecise` -- and the LIST IS EMPTY. It is
            // load-bearing over there for a reason that cannot exist here: a
            // reallocation inside emit-all-defs' save/restore bracket lands in
            // scratch the bracket reclaims. Nothing here reclaims anything.
            ("__list-with-capacity", [Int(_)]) => Ok(list(Vec::new())),
            // **THE ONE WRITER.** It answers the list it was handed, which is
            // the same list the caller still holds -- see `Value::List`.
            ("list-set-at", [List(xs), Int(i), v]) => {
                let i = *i as usize;
                let mut cells = xs.borrow_mut();
                if i >= cells.len() {
                    return err(format!("list-set-at {i} past the end"));
                }
                cells[i] = v.clone();
                drop(cells);
                Ok(List(xs.clone()))
            }

            // -- arithmetic ---------------------------------------------------
            // `negate : forall a. a -> a` -- polymorphic upstream, and the one
            // arithmetic builtin that is. `abs`, `max` and `min` are Integer
            // only, and stay that way.
            ("negate", [Int(i)]) => Ok(Int(-i)),
            ("negate", [Real(f)]) => Ok(Real(-f)),
            ("abs", [Int(i)]) => Ok(Int(i.abs())),
            ("max", [Int(a), Int(b)]) => Ok(Int(*a.max(b))),
            ("min", [Int(a), Int(b)]) => Ok(Int(*a.min(b))),
            ("int-mod", [Int(a), Int(b)]) if *b != 0 => Ok(Int(a.rem_euclid(*b))),
            ("int-rem", [Int(a), Int(b)]) if *b != 0 => Ok(Int(a % b)),
            ("int-mod" | "int-rem", [Int(_), Int(_)]) => err("modulo by zero"),
            ("bit-and", [Int(a), Int(b)]) => Ok(Int(a & b)),
            ("bit-or", [Int(a), Int(b)]) => Ok(Int(a | b)),
            ("bit-xor", [Int(a), Int(b)]) => Ok(Int(a ^ b)),
            ("bit-not", [Int(a)]) => Ok(Int(!a)),
            ("bit-shl", [Int(a), Int(b)]) => Ok(Int(((*a as u64) << (*b as u32 & 63)) as i64)),
            ("bit-shr" | "bit-shru", [Int(a), Int(b)]) => {
                Ok(Int(((*a as u64) >> (*b as u32 & 63)) as i64))
            }
            ("text-split", [Text(t), Text(sep)]) => Ok(list(
                if sep.is_empty() {
                    vec![Text(t.clone())]
                } else {
                    let parts: Vec<String> =
                        t.split(sep.as_str()).map(|p| p.to_string()).collect();
                    let mut out = Vec::with_capacity(parts.len());
                    for part in parts {
                        out.push(self.text(part)?);
                    }
                    return Ok(list(out));
                },
            )),

            // -- reals --------------------------------------------------------
            // ONE ARM FOR EIGHT NAMES WAS WRONG ABOUT FIVE OF THEM. Only the
            // two `*-from-int` take an Integer; the rest take a REAL, so the
            // arm never matched and they failed as "no rule for (a real)".
            // `to-real` is not a builtin at all. The declared types:
            //
            //   real-from-int              Integer -> f64
            //   real-approx-from-int       Integer -> f32   <- NARROWS
            //   to-real-approx             f64     -> f32   <- NARROWS
            //   to-real-trapping           f64     -> f64-trapping
            //   to-real-saturating         f64     -> f64-saturating
            //   to-real-approx-trapping    f32     -> f32-trapping
            //   to-real-approx-saturating  f32     -> f32-saturating
            //
            // The trapping and saturating ones change the OVERFLOW MODE and
            // not the value, so they are the identity here; the two that end
            // in f32 must round through f32 or a large value comes back with
            // digits an f32 cannot hold.
            ("real-from-int", [Int(i)]) => Ok(Real(*i as f64)),
            ("real-approx-from-int", [Int(i)]) => Ok(Real(*i as f32 as f64)),
            ("to-real-approx", [Real(f)]) => Ok(Real(*f as f32 as f64)),
            // The `from-real-*` direction WIDENS or drops an overflow mode --
            // `from-real-approx : f32 -> f64`, `from-real-trapping :
            // f64-trapping -> f64`. Every Real here is already an f64, and the
            // f32 ones arrived rounded, so each is the identity on the value.
            (
                "from-real-approx"
                | "from-real-approx-trapping"
                | "from-real-approx-saturating"
                | "from-real-trapping"
                | "from-real-saturating",
                [Real(f)],
            ) => Ok(Real(*f)),
            (
                "to-real-trapping"
                | "to-real-saturating"
                | "to-real-approx-trapping"
                | "to-real-approx-saturating",
                [Real(f)],
            ) => Ok(Real(*f)),
            ("real-approx-to-int", [Real(f)]) => Ok(Int(*f as i64)),
            ("real-approx-to-bits", [Real(f)]) => Ok(Int((*f as f32).to_bits() as i64)),
            ("bits-to-real-approx", [Int(i)]) => Ok(Real(f32::from_bits(*i as u32) as f64)),
            ("real-to-int", [Real(f)]) => Ok(Int(*f as i64)),
            ("real-to-bits", [Real(f)]) => Ok(Int(f.to_bits() as i64)),
            ("bits-to-real", [Int(i)]) => Ok(Real(f64::from_bits(*i as u64))),

            // -- compiler intrinsics ------------------------------------------
            // `__narrow` is a codegen hint: it tells the emitter a value fits
            // a narrower machine type. At the value level it is the identity.
            ("__narrow", [v]) => Ok(v.clone()),

            // -- the allocator, as arithmetic ---------------------------------
            // See `heap_pos` on the struct for why these move rather than
            // answering a constant, and for what this arm consequently cannot
            // see. `__heap-advance` and `__heap-restore` are declared to answer
            // Nothing and the compiler binds their results only to sequence
            // them, so Unit is the whole of it.
            // THE HOST IS A HOSTED ONE. `hosted-kind` is 1 in the zig, wasm and
            // C# plugs and 0 in the bare-metal code generators, and it guards
            // the memory work a hosted target has no business doing -- the
            // check compact above all. A tree walker is as hosted as it gets.
            ("hosted-kind", []) => Ok(Int(1)),
            // AN IDENTITY FOR A VALUE THAT HAS NO ADDRESS.
            //
            // Upstream emits `address-of` as the identity -- the value with no
            // load -- so an Integer answers itself, and measured on real x86 a
            // payload-free constructor is BOXED and answers its own heap
            // pointer, 24 bytes from its neighbour. The compiler uses it for
            // ABSENCE: `address-of x == 0` is how ten tests in `Types/Unifier`
            // ask whether there is a value at all.
            //
            // So an integer answers itself and everything else answers a
            // stable non-zero id. The pointer inside the `Rc` is exactly that,
            // and now that records are shared it has the right property too:
            // two names for one record answer the same id, as they do on bare
            // metal. What it is NOT is bare metal's number, and nothing may
            // compare it across arms or embed it in output.
            ("address-of", [Int(i)]) => Ok(Int(*i)),
            ("address-of", [Record(_, fs)]) => Ok(Int(Rc::as_ptr(fs) as i64)),
            ("address-of", [List(xs)]) => Ok(Int(Rc::as_ptr(xs) as *const u8 as i64)),
            ("address-of", [Ctor(_, fs)]) => Ok(Int(Rc::as_ptr(fs) as *const u8 as i64)),
            // **A TEXT ANSWERS WHERE IT WAS ALLOCATED**, from the same cursor
            // `__heap-save` reads. This was the host pointer, and the host
            // pointer is on a scale five orders of magnitude above every base
            // the compiler computes -- so `copy-sx-text`'s durability test was
            // false for every text, always, and the source was rebuilt at
            // every keep boundary. That was the whole of a 2.3 GB peak on a
            // 112 KB subject.
            ("address-of", [Text(t)]) => Ok(Int(t.addr)),
            ("address-of", [Unit]) => Ok(Int(0)),
            // The tag the unifier reads. Upstream's `mcopy-type` read this out
            // of raw memory and took a payload word for it, which was the root
            // of issue 126; here it is the declaration order and cannot be
            // anything else.
            ("variant-tag", [Ctor(n, _)]) => Ok(Int(*self.tags.get(n).unwrap_or(&0))),
            ("variant-tag", [Int(i)]) => Ok(Int(*i)),
            ("tag-equal", [Ctor(a, _), Ctor(b, _)]) => Ok(Bool(a == b)),
            ("text-concat-list", [List(xs)]) => {
                let mut out = String::new();
                for x in xs.borrow().iter() {
                    match x {
                        Text(t) => out.push_str(t),
                        other => return err(format!("text-concat-list over {}", type_name(other))),
                    }
                }
                self.text(out)
            }
            // The deck bracket: everything allocated between them is scratch
            // the exit reclaims. Nothing here reclaims anything, so the bracket
            // is a pair of no-ops -- which is exactly why this arm cannot see
            // a value that outlives one.
            ("__deck-enter", []) => {
                self.bump.enter();
                Ok(Unit)
            }
            ("__deck-exit", []) => {
                self.bump.exit();
                Ok(Unit)
            }
            // **A LINKED LIST IS A LIST, and there is no second variant.**
            //
            // There WAS one, for the eleven days a `List` was immutable: a
            // separate mutable handle so `ChapterScoper`'s accumulator could be
            // pushed into. `cx_ll_push` is the emitter for BOTH -- it is the
            // same function, `l.items.append(gpa, v); return l;` -- and once
            // `list-push` writes through, the two variants held the same value
            // and behaved the same way. The distinction is real upstream and it
            // is in the TYPE (`LinkedListTy`, not `list`); it was never in the
            // representation, and `ChapterScoper` seeds its `LinkedList ADef`
            // with `[]` because at the value level there is nothing to seed it
            // with but an empty list.
            //
            // The capacity is a hint upstream and there is nothing here to
            // reserve, exactly as with `__list-with-capacity`.
            ("__linked-list-empty", [Int(_)]) => Ok(list(Vec::new())),
            ("__linked-list-push", [List(xs), v]) => {
                xs.borrow_mut().push(v.clone());
                Ok(List(xs.clone()))
            }
            ("__linked-list-to-list", [List(xs)]) => Ok(List(xs.clone())),

            // **A DECIMAL LITERAL TO THE DOUBLE NEAREST IT.** Rust's `parse`
            // is correctly rounded and upstream's `text-to-double-bits` is
            // not: issue 125 has it right to fifteen significant digits and
            // wrong above 2^53, where the routine's own accumulation loses a
            // bit before the rounding step ever runs. So this arm is EXPECTED
            // to disagree with the bank on any program carrying such a
            // literal, and the disagreement is the better answer. Three safari
            // specs already carry the same gap against the zig arm, filed in
            // `spec/arm-gaps.tsv`.
            //
            // A literal the parse refuses is not a hosting gap: the lexer only
            // reaches here with text it has already accepted as a Real.
            ("text-to-double-bits", [Text(t)]) => match t.trim().parse::<f64>() {
                Ok(f) => Ok(Int(f.to_bits() as i64)),
                Err(_) => err(format!("text-to-double-bits on {t:?}, which is not a Real")),
            },

            // **THE WHOLE FILE, OR AN ERROR.** `cx_read_file_uni` panics on a
            // path it cannot open and on a read that fails, and this refuses
            // for the same reason: a missing subject that reads as an empty
            // text is a compile of nothing that reports success.
            //
            // It goes through `self.text`, so the contents get an address like
            // any other text -- the source a compile is about is the single
            // biggest thing `copy-sx-text` will be asked about, and it has to
            // be able to answer.
            ("read-file-uni", [Text(path)]) => match std::fs::read(path.as_str()) {
                Ok(bytes) => {
                    let t = String::from_utf8_lossy(&bytes).into_owned();
                    self.text(t)
                }
                Err(e) => err(format!("read-file-uni {:?}: {e}", path.as_str())),
            },

            // **A HOSTED COMPILER HAS NO SELF TYPE TABLE, and answers the
            // EMPTY list.** Bare metal fills this from the type definitions it
            // was itself built with, which is how `pmap-selftest` resolves a
            // root type by name. Both plugs decline the same way and say so in
            // their name tables -- zig maps it to `cx_ll_empty(TypeBinding)`
            // and wasm to `list_with_capacity 0` -- so the empty answer is the
            // fixed point rather than a gap here.
            ("__self-type-defs", []) => Ok(list(Vec::new())),

            // -- the flat memory ---------------------------------------------
            // Every one of these takes a BASE and an OFFSET and adds them, so
            // `peek-32 slot 0` is the shape a caller who already did the
            // arithmetic writes. A poke answers 0; `__memset` answers nothing.
            ("peek-byte", [Int(b), Int(o)]) => Ok(Int(self.mem.load(b + o, 1))),
            ("peek-16", [Int(b), Int(o)]) => Ok(Int(self.mem.load(b + o, 2))),
            ("peek-32", [Int(b), Int(o)]) => Ok(Int(self.mem.load(b + o, 4))),
            ("peek-qword", [Int(b), Int(o)]) => Ok(Int(self.mem.load(b + o, 8))),
            ("poke-byte", [Int(b), Int(o), Int(v)]) => {
                self.mem.store(b + o, 1, *v);
                Ok(Int(0))
            }
            ("poke-16", [Int(b), Int(o), Int(v)]) => {
                self.mem.store(b + o, 2, *v);
                Ok(Int(0))
            }
            ("poke-32", [Int(b), Int(o), Int(v)]) => {
                self.mem.store(b + o, 4, *v);
                Ok(Int(0))
            }
            ("poke-qword", [Int(b), Int(o), Int(v)]) => {
                self.mem.store(b + o, 8, *v);
                Ok(Int(0))
            }
            // **A HOSTED PROCESS HAS NO I/O PORTS**, and the zig plug's
            // `cx_port_out_byte` answers 0 without writing. An MMIO poke is
            // the same question: it takes its arguments so a caller's own
            // side effects still happen, and writes nothing.
            ("poke-mmio" | "poke-mmio-32", [Int(_), Int(_), Int(_)]) => Ok(Int(0)),
            // `__memset` fills n bytes with the LOW BYTE of its value. The
            // checker opens every batch by zeroing its cons table this way.
            ("__memset", [Int(b), Int(v), Int(n)]) => {
                self.mem.fill(*b, *n, *v as u8);
                Ok(Unit)
            }

            // `__heap-save` reads the ACTIVE cursor, which is the whole of
            // what makes a guarded copy's `__heap-save >= ceiling` mean
            // anything: inside an extent it asks about the deck, outside it
            // asks about the bivy.
            ("__heap-save", []) => Ok(Int(self.cursor())),
            ("__heap-advance", [Int(n)]) => {
                let c = self.cursor() + *n;
                self.set_cursor(c);
                Ok(Unit)
            }
            ("__heap-restore", [Int(p)]) => {
                self.set_cursor(*p);
                Ok(Unit)
            }
            // The CELL, which is frozen for as long as an extent is open.
            ("__deck-pos", []) => Ok(Int(self.bump.deck_pos())),
            ("__deck-set", [Int(p)]) => {
                self.bump.deck_set(*p);
                Ok(Unit)
            }
            // `__record-set` is how a mutable record is updated: record, field
            // NAME as text, value.
            ("__record-set", [Record(n, fs), Text(field), v]) => {
                // Same mutation as `Code::FieldAssign`, with the field named
                // by a VALUE rather than by the source.
                let mut out = fs.borrow_mut();
                // **The field is named by a VALUE here, not by the source**, so
                // this is the one place a name is not already in the table --
                // and the one reason the interpreter keeps a mutable one. A
                // field named by a text nothing else mentions is a new symbol.
                let n = *n;
                let key = self.syms.intern(field);
                let bound = self.bounds.get(&(n, key));
                let v = match (v, bound) {
                    (Int(i), Some(b)) => Int(apply_bound(*i, b)),
                    _ => v.clone(),
                };
                match out.iter_mut().find(|(k, _)| *k == key) {
                    Some(slot) => slot.1 = v,
                    None => out.push((key, v)),
                }
                drop(out);
                Ok(Record(n, fs.clone()))
            }

            // NOT "is not interpreted yet" -- this arm cannot tell an absent
            // builtin from one that is here and was handed the wrong things,
            // and asserting the first hid the second. `bit-and` reached here
            // as ``not interpreted yet (given a function, an integer)`` while
            // being fully implemented; the argument types are the finding and
            // they go in front.
            _ => err(format!(
                "builtin `{name}` has no rule for ({})",
                args.iter().map(type_name).collect::<Vec<_>>().join(", ")
            )),
        }
    }
}

/// `float-to-ordinal`: a float's bits as a monotonically ordered integer, so
/// that subtracting two of them counts the representable values between --
/// ULPs. Negative floats have their low 63 bits flipped and one added, which
/// is what turns sign-magnitude into two's complement order.
fn ordinal(f: f64) -> i64 {
    let bits = f.to_bits() as i64;
    if bits < 0 {
        (bits ^ 0x7FFF_FFFF_FFFF_FFFF).wrapping_add(1)
    } else {
        bits
    }
}

/// `char-code`, the private frequency-ordered alphabet. NOT ASCII.
fn char_code(b: u8) -> i64 {
    if (b as usize) < crate::charcode::CHAR_CODE.len() {
        crate::charcode::CHAR_CODE[b as usize] as i64
    } else {
        0
    }
}

fn code_to_char(code: i64) -> char {
    crate::charcode::CHAR_CODE
        .iter()
        .position(|c| *c as i64 == code && code != 0)
        .map(|b| b as u8 as char)
        .unwrap_or('\0')
}

fn apply_bound(v: i64, b: &FieldBound) -> i64 {
    match b.mode {
        OverflowMode::Clamping => v.clamp(b.lo, b.hi),
        OverflowMode::Wrapping => {
            let span = b.hi - b.lo + 1;
            if span <= 0 {
                v
            } else {
                b.lo + (v - b.lo).rem_euclid(span)
            }
        }
        // `error` is a compile-time refusal, not a runtime one.
        OverflowMode::Error => v,
    }
}

pub(crate) fn literal(text: &str, kind: LiteralKind) -> R<Value> {
    match kind {
        // `#FFFF` is hexadecimal. The lexer scans it as one integer literal,
        // hash and all.
        LiteralKind::IntLit => {
            let clean = text.replace('_', "");
            match clean.strip_prefix('#') {
                // THROUGH u64, NOT i64. `#8000000000000000` is sixteen digits
                // and sets the sign bit, which `i64::from_str_radix` refuses as
                // out of range -- so the one literal a program writes to mean
                // "the most negative integer" was the one that would not parse.
                // A hexadecimal literal names a BIT PATTERN, and the pattern is
                // 64 bits wide either way round.
                Some(hex) => u64::from_str_radix(hex, 16)
                    .map(|u| Value::Int(u as i64))
                    .map_err(|_| Error(format!("bad hex literal `{text}`"))),
                None => clean
                    .parse()
                    .map(Value::Int)
                    .map_err(|_| Error(format!("bad integer literal `{text}`"))),
            }
        }
        LiteralKind::NumLit => text
            .replace('_', "")
            .parse()
            .map(Value::Real)
            .map_err(|_| Error(format!("bad number literal `{text}`"))),
        LiteralKind::BoolLit => Ok(Value::Bool(text == "True")),
        LiteralKind::TextLit => {
            let s = unescape(text);
            let addr = crate::bump::intern_literal(s.len() as i64);
            Ok(Value::Text(Rc::new(Str { addr, s })))
        }
        LiteralKind::CharLit => Ok(Value::Char(unescape(text).chars().next().unwrap_or('\0'))),
    }
}

/// A text literal arrives with its quotes and escapes as written.
fn unescape(raw: &str) -> String {
    let body = raw.strip_prefix('"').and_then(|s| s.strip_suffix('"')).unwrap_or_else(|| {
        raw.strip_prefix('\'').and_then(|s| s.strip_suffix('\'')).unwrap_or(raw)
    });
    let mut out = String::with_capacity(body.len());
    let mut it = body.chars();
    while let Some(c) = it.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match it.next() {
            Some('n') => out.push('\n'),
            Some('\\') => out.push('\\'),
            Some('"') => out.push('"'),
            Some('\'') => out.push('\''),
            Some(other) => out.push(other),
            None => {}
        }
    }
    out
}

/// **CONCATENATION ALLOCATES, so this needs the allocator.** `&` on two texts
/// is a fresh block at the cursor upstream -- bare metal's two str-concat
/// emitters both bump r10 unconditionally, and the zig plug documents why it
/// does not short-circuit an empty right operand: an aliased return inside a
/// deck extent yields a value that looks decked and is not.
///
/// The borrow is split rather than the table cloned: `syms` and `bump` are
/// disjoint fields, and Rust will let both be borrowed at once when it can see
/// that.
fn binary(syms: &SymTab, bump: &mut crate::bump::Bump, op: BinaryOp, a: Value, b: Value) -> R<Value> {
    let mut cat = |s: String| {
        let addr = bump.alloc(s.len() as i64);
        Text(Rc::new(Str { addr, s }))
    };
    use BinaryOp::*;
    use Value::*;
    Ok(match (op, &a, &b) {
        (OpAdd, Int(x), Int(y)) => Int(x + y),
        (OpSub, Int(x), Int(y)) => Int(x - y),
        (OpMul, Int(x), Int(y)) => Int(x * y),
        (OpDiv, Int(x), Int(y)) if *y != 0 => Int(x / y),
        (OpDiv, Int(_), Int(_)) => return err("division by zero"),
        (OpPow, Int(x), Int(y)) => Int(x.pow(*y as u32)),
        (OpAdd, Real(x), Real(y)) => Real(x + y),
        (OpSub, Real(x), Real(y)) => Real(x - y),
        (OpMul, Real(x), Real(y)) => Real(x * y),
        (OpDiv, Real(x), Real(y)) => Real(x / y),
        (OpLt, Int(x), Int(y)) => Bool(x < y),
        (OpGt, Int(x), Int(y)) => Bool(x > y),
        (OpLtEq, Int(x), Int(y)) => Bool(x <= y),
        (OpGtEq, Int(x), Int(y)) => Bool(x >= y),
        (OpLt, Real(x), Real(y)) => Bool(x < y),
        (OpGt, Real(x), Real(y)) => Bool(x > y),
        (OpLtEq, Real(x), Real(y)) => Bool(x <= y),
        (OpGtEq, Real(x), Real(y)) => Bool(x >= y),
        (OpPow, Real(x), Real(y)) => Real(x.powf(*y)),
        (OpBoolAnd, Bool(x), Bool(y)) => Bool(*x && *y),
        (OpOr, Bool(x), Bool(y)) => Bool(*x || *y),
        // `~` and `~0` are ULP comparisons, not tolerances. `float-to-ordinal`
        // maps a float's bits to a monotonic integer -- flip the low 63 bits
        // and add one when negative -- and then `~` asks for a difference of
        // at most 4 and `~0` for exactly 0. Nothing about the operator says
        // "four"; it is a constant in the emitter.
        (OpApproxEq, Real(x), Real(y)) => Bool((ordinal(*x) - ordinal(*y)).abs() <= 4),
        (OpApproxEqExact, Real(x), Real(y)) => Bool(ordinal(*x) == ordinal(*y)),
        (OpEq, _, _) => Bool(equal(&a, &b)),
        (OpNotEq, _, _) => Bool(!equal(&a, &b)),
        (OpDefEq, _, _) => Bool(equal(&a, &b)),
        // `&` is one operator with four meanings, chosen by what it is given.
        (OpAnd | OpAppend, Text(x), Text(y)) => cat(format!("{x}{y}")),
        (OpAnd | OpAppend, Text(x), _) => cat(format!("{x}{}", show(syms, &b))),
        (OpAnd | OpAppend, _, Text(y)) => cat(format!("{}{y}", show(syms, &a))),
        (OpAnd | OpAppend, List(x), List(y)) => {
            let mut out = x.borrow().clone();
            out.extend(y.borrow().iter().cloned());
            list(out)
        }
        (OpAnd, Bool(x), Bool(y)) => Bool(*x && *y),
        (OpAnd, Int(x), Int(y)) => Int(x & y),
        (OpOr, Int(x), Int(y)) => Int(x | y),
        (OpCons, _, List(y)) => {
            let mut out = vec![a.clone()];
            out.extend(y.borrow().iter().cloned());
            list(out)
        }
        _ => {
            return err(format!(
                "{:?} on {} and {}",
                op,
                type_name(&a),
                type_name(&b)
            ))
        }
    })
}

fn equal(a: &Value, b: &Value) -> bool {
    use Value::*;
    match (a, b) {
        (Int(x), Int(y)) => x == y,
        (Real(x), Real(y)) => x == y,
        (Text(x), Text(y)) => x.as_str() == y.as_str(),
        (Char(x), Char(y)) => x == y,
        (Bool(x), Bool(y)) => x == y,
        (Unit, Unit) => true,
        (List(x), List(y)) => {
            if Rc::ptr_eq(x, y) {
                return true;
            }
            let (x, y) = (x.borrow(), y.borrow());
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| equal(p, q))
        }
        (Ctor(n, x), Ctor(m, y)) => {
            n == m && x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| equal(p, q))
        }
        (Record(n, x), Record(m, y)) => {
            let (x, y) = (x.borrow(), y.borrow());
            n == m
                && x.len() == y.len()
                && x.iter().zip(y.iter()).all(|(p, q)| p.0 == q.0 && equal(&p.1, &q.1))
        }
        _ => false,
    }
}

/// Match, pushing each bound value in the order the compiler counted the
/// pattern's variables -- which is what makes a slot implicit rather than
/// named. A failing sub-pattern leaves a partly filled frame behind, and it is
/// thrown away with the arm.
fn matches_pat(v: &Value, p: &PatCode, vals: &mut Vec<Value>) -> bool {
    match p {
        PatCode::Wild => true,
        PatCode::Var => {
            vals.push(v.clone());
            true
        }
        PatCode::Lit(l) => equal(v, l),
        PatCode::BadLit => false,
        PatCode::Ctor(name, subs) => match v {
            Value::Ctor(n, fields) if *n == *name => {
                subs.len() == fields.len()
                    && subs.iter().zip(fields.iter()).all(|(s, f)| matches_pat(f, s, vals))
            }
            // A one-field constructor pattern over a bare value is how the
            // tuple patterns land after desugaring.
            Value::Record(n, fields) if *n == *name => {
                let fields = fields.borrow();
                subs.len() == fields.len()
                    && subs.iter().zip(fields.iter()).all(|(s, f)| matches_pat(&f.1, s, vals))
            }
            _ => false,
        },
        PatCode::Vec_(subs) => match v {
            Value::List(xs) => {
                let xs = xs.borrow();
                subs.len() == xs.len()
                    && subs.iter().zip(xs.iter()).all(|(s, x)| matches_pat(x, s, vals))
            }
            _ => false,
        },
    }
}

pub fn show(syms: &SymTab, v: &Value) -> String {
    match v {
        Value::Int(i) => i.to_string(),
        Value::Real(f) => format!("{f}"),
        Value::Text(t) => t.as_str().to_string(),
        Value::Char(c) => c.to_string(),
        Value::Bool(b) => if *b { "True" } else { "False" }.to_string(),
        Value::Unit => String::new(),
        Value::List(xs) => {
            let inner: Vec<String> = xs.borrow().iter().map(|x| show(syms, x)).collect();
            format!("[{}]", inner.join(", "))
        }
        Value::Ctor(n, fs) if fs.is_empty() => syms.text(*n).to_string(),
        Value::Ctor(n, fs) => {
            let inner: Vec<String> = fs.iter().map(|x| show(syms, x)).collect();
            format!("{} {}", syms.text(*n), inner.join(" "))
        }
        Value::Record(n, fs) => {
            let inner: Vec<String> = fs
                .borrow()
                .iter()
                .map(|(k, v)| format!("{} = {}", syms.text(*k), show(syms, v)))
                .collect();
            format!("{} {{ {} }}", syms.text(*n), inner.join(", "))
        }
        Value::Fun(_) => "<function>".to_string(),
    }
}

fn type_name(v: &Value) -> &'static str {
    match v {
        Value::Int(_) => "an integer",
        Value::Real(_) => "a real",
        Value::Text(_) => "a text",
        Value::Char(_) => "a char",
        Value::Bool(_) => "a boolean",
        Value::List(_) => "a list",
        Value::Record(..) => "a record",
        Value::Ctor(..) => "a constructor",
        Value::Fun(_) => "a function",
        Value::Unit => "nothing",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// **A variant that grows `Value` costs more than the allocations it can
    /// save**, and this number is the record of learning that the hard way.
    ///
    /// It was 24 bytes when a record's type name was an `Rc<String>`. Interning
    /// those names as `Rc<str>` removed 1.59 million allocations from one
    /// safari unit and ran 16% SLOWER, because `Rc<str>` is a FAT pointer: it
    /// took the largest variant from 16 bytes to 24 and this enum from 24 to
    /// 32, and every step moves `Value`s. `Rc<String>` kept it thin and won 6%.
    /// Symbols then took the largest variant -- `Record(Sym, Rc<Vec<..>>)` --
    /// down to 12, and the enum to 16. Two words.
    #[test]
    fn value_is_two_words() {
        assert_eq!(std::mem::size_of::<Value>(), 16);
    }

    /// Run a whole chapter and answer what it printed.
    ///
    /// The tests below are all about ONE construct -- assignment to a record
    /// field -- because it is the one the compiler's own lexer is built out of
    /// and the one nothing else in this ecosystem uses. safari's port, judge
    /// and specs contain ZERO field assignments across 54 chapters, which is
    /// why 2,351 graded values on three arms never touched this path.
    fn out(src: &str) -> String {
        let src = src.as_bytes().to_vec();
        let parsed = crate::parser::parse(&src);
        let mut dg = crate::desugar::Desugar::new(&src);
        let ch = dg.chapter(&parsed.tree);
        let mut it = Interp::new(&ch);
        it.run().unwrap_or_else(|e| panic!("{}", e.0));
        it.out
    }

    const BOX: &str = "Chapter: T\n\nSection: S\n\n  Box = record {\n    n : Integer,\n    m : Integer\n  }\n\n";

    /// **The bug that interpreting Cobblestone's lexer found.** A field
    /// assignment writes THROUGH: the record the caller holds sees it, because
    /// `scan-ident-rest` assigns `st.offset` and then returns the same `st`.
    #[test]
    fn a_field_assignment_is_visible_in_the_caller() {
        let src = format!(
            "{BOX}  bump : Box -> Box\n  bump (b) =\n    let __seq = b.n = 99\n    in b\n\n\
             Section: E\n\n  opening : [Console] Nothing = act\n                 let a = Box {{ n = 1, m = 2 }}\n    in let r = bump a\n                 in print-line-uni (show (r.n) & \" \" & show (a.n) & \" \" & show (a.m))\n  end\n"
        );
        assert_eq!(out(&src).trim(), "99 99 2");
    }

    /// The field name is the token AFTER the dot, and a trailing newline is not
    /// it. Taking the last non-trivia token gave the assignment a field named
    /// "\n" -- the record grew a second, nameless field and the real one kept
    /// its value. Two fields here so a mis-named write cannot land on the right
    /// one by luck.
    #[test]
    fn the_assigned_field_is_the_one_after_the_dot() {
        let src = format!(
            "{BOX}Section: E\n\n  opening : [Console] Nothing = act\n                 let a = Box {{ n = 1, m = 2 }}\n    in let __seq = a.m = 7\n                 in print-line-uni (show a)\n  end\n"
        );
        assert_eq!(out(&src).trim(), "Box { n = 1, m = 7 }");
    }

    /// Records are SHARED, so two names for one record both see the write.
    /// This is the property the rebind-the-name alternative could not give and
    /// could not fail loudly about.
    #[test]
    fn two_names_for_one_record_see_the_same_write() {
        let src = format!(
            "{BOX}Section: E\n\n  opening : [Console] Nothing = act\n                 let a = Box {{ n = 1, m = 2 }}\n    in let b = a\n                 in let __seq = a.n = 5\n                 in print-line-uni (show (b.n))\n  end\n"
        );
        assert_eq!(out(&src).trim(), "5");
    }

    /// A record LITERAL is a fresh record every time, so sharing is not
    /// accidental: two literals with the same fields are two records.
    #[test]
    fn two_literals_are_two_records() {
        let src = format!(
            "{BOX}Section: E\n\n  opening : [Console] Nothing = act\n                 let a = Box {{ n = 1, m = 2 }}\n    in let b = Box {{ n = 1, m = 2 }}\n                 in let __seq = a.n = 5\n                 in print-line-uni (show (b.n))\n  end\n"
        );
        assert_eq!(out(&src).trim(), "1");
    }

    /// `scan-ident-rest` in miniature: a tail-recursive scanner that advances
    /// by assigning a field and returning the record it was handed. Before the
    /// fix this did not terminate.
    #[test]
    fn a_scanner_that_advances_by_assignment_terminates() {
        let src = format!(
            "{BOX}  step : Box -> Box\n  step (b) =\n                 if b.n >= b.m then b\n                 else let __seq = b.n = b.n + 1\n    in step b\n\n             Section: E\n\n  opening : [Console] Nothing = act\n                 let a = Box {{ n = 0, m = 40 }}\n    in print-line-uni (show ((step a).n))\n  end\n"
        );
        assert_eq!(out(&src).trim(), "40");
    }

    // ---- the allocator's arithmetic ------------------------------------
    //
    // `codex/compiler/Core/PhaseAllocator.codex` IS the specification and these
    // transcribe it. A test failing here means this arm's counters do not obey
    // the contract the compiler is written against -- not that the contract is
    // unclear.
    //
    // The compiler manages its own memory with a BIVY that bumps upward and a
    // DECK reserved out of it in one advance. This arm allocates nothing, so
    // what has to be right is the arithmetic the compiler's own guards read.

    /// The allocator chapter's primitives, transcribed, for the tests to call.
    const ALLOC: &[&str] = &[
        "  pitch : Integer -> Integer",
        "  pitch (size) =",
        "   let p = __heap-save",
        "   in let advanced = __heap-advance size",
        "   in p",
        "",
        "  strike : Integer -> Nothing",
        "  strike (start) = __heap-restore start",
        "",
        "  build : Integer -> Integer",
        "  build (size) =",
        "   let p = __heap-save",
        "   in let deck-init = __deck-set p",
        "   in let advanced = __heap-advance size",
        "   in p",
        "",
        "  init-phase-allocator : Integer",
        "  init-phase-allocator =",
        "   let base = __heap-save",
        "   in let deck-init = __deck-set base",
        "   in base",
        "",
        "  phase-compact : Nothing = __heap-restore (__deck-pos)",
        "",
        "  deck-short-of : Integer, Integer -> Boolean",
        "  deck-short-of (ceiling) (band) =",
        "   if ceiling > 0 & __deck-pos + band >= ceiling then True else False",
        "",
        "  deck-bound-short-of : Integer, Integer -> Boolean",
        "  deck-bound-short-of (ceiling) (band) =",
        "   if ceiling > 0 & __heap-save + band >= ceiling then True else False",
        "",
    ];

    /// **POSITIONS ARE REPORTED FROM THE HEAP ORIGIN**, because the origin is
    /// a constant of the model and not of the behaviour under test.
    ///
    /// The heap does not start at zero -- it starts at `bump::HEAP_ORIGIN`, so
    /// that the band below it can hold text literals, which are durable and
    /// must compare below every base. These tests are about how far the cursor
    /// MOVES, and writing that constant into eleven expected strings would
    /// have made them a record of where the heap happens to begin rather than
    /// of what the allocator does.
    ///
    /// Every integer in the output is a position; anything that does not parse
    /// as one is left alone, which is how `True` survives.
    fn from_origin(out: String) -> String {
        out.split_whitespace()
            .map(|w| match w.parse::<i64>() {
                Ok(n) => (n - crate::bump::HEAP_ORIGIN).to_string(),
                Err(_) => w.to_string(),
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    /// Run `body` as the entry point, with the allocator primitives in scope.
    fn alloc_out(body: &[&str]) -> String {
        let mut lines: Vec<String> =
            vec!["Chapter: A".into(), "".into(), "Section: S".into(), "".into()];
        lines.extend(ALLOC.iter().map(|l| (*l).to_string()));
        lines.push("Section: E".into());
        lines.push("".into());
        lines.push("  opening : [Console] Nothing = act".into());
        lines.extend(body.iter().map(|l| format!("    {l}")));
        lines.push("  end".into());
        out(&lines.join("\n")).trim().to_string()
    }

    /// `alloc_out`, for a body whose output is POSITIONS. Kept separate
    /// because `alloc_out` is also the scaffolding for tests that print list
    /// lengths, and subtracting an origin from a count of two gives
    /// -16777214 -- which is what happened when this normalisation was
    /// applied to every caller instead of the ones that meant it.
    fn alloc_pos(body: &[&str]) -> String {
        from_origin(alloc_out(body))
    }

    /// `pitch` answers where the bivy was and leaves it `size` higher; `strike`
    /// puts it back exactly.
    #[test]
    fn pitch_answers_the_old_frontier_and_strike_restores_it() {
        assert_eq!(
            alloc_pos(&[
                "let a = pitch 100",
                "in let b = pitch 50",
                "in let c = __heap-save",
                "in let __x = strike a",
                "in let d = __heap-save",
                "in print-line-uni (show a & \" \" & show b & \" \" & show c & \" \" & show d)",
            ]),
            "0 100 150 0"
        );
    }

    /// `build` reserves the whole deck in ONE advance -- the reason the guard
    /// page cannot catch it, and the reason that chapter checks it instead --
    /// and it plants the deck cursor at the reservation's base.
    #[test]
    fn build_plants_the_deck_at_the_base_and_advances_the_bivy_over_it() {
        assert_eq!(
            alloc_pos(&[
                "let base = build 1000",
                "in let top = __heap-save",
                "in let deck = __deck-pos",
                "in print-line-uni (show base & \" \" & show top & \" \" & show deck)",
            ]),
            "0 1000 0"
        );
    }

    /// `phase-compact` is `__heap-restore (__deck-pos)`: it drops the bivy back
    /// to the deck's base, which is what makes a phase's scratch free.
    #[test]
    fn phase_compact_drops_the_bivy_to_the_deck() {
        assert_eq!(
            alloc_pos(&[
                "let base = build 1000",
                "in let __a = pitch 400",
                "in let grown = __heap-save",
                "in let __b = phase-compact",
                "in let after = __heap-save",
                "in print-line-uni (show grown & \" \" & show after & \" \" & show base)",
            ]),
            "1400 0 0"
        );
    }

    /// **THE GUARD ASKS ABOUT THE FLOOR'S WIDTH, NOT ABOUT USAGE**, and the
    /// chapter says so outright: inside a phase-wide extent the deck-pos cell is
    /// FROZEN at the base, so `deck-short-of` reduces to
    /// `base + band >= base + height` -- "true only when the floor is narrower
    /// than the band".
    ///
    /// This is the assertion the model turns on. The parse phase reserves a
    /// 392 MB floor against an 8 MB band, so it must answer False.
    #[test]
    fn deck_short_of_is_false_while_the_floor_is_wider_than_the_band() {
        assert_eq!(
            alloc_out(&[
                "let base = build 411041792",
                "in let wide = deck-short-of (base + 411041792) 8388608",
                "in let narrow = deck-short-of (base + 4194304) 8388608",
                "in let unarmed = deck-short-of 0 8388608",
                "in print-line-uni (show wide & \" \" & show narrow & \" \" & show unarmed)",
            ]),
            "False True False"
        );
    }

    /// `deck-bound-short-of` asks the same shape of the BIVY frontier, and the
    /// two answer differently on purpose: the bivy has moved over the whole
    /// reservation and the deck has not moved at all.
    #[test]
    fn the_bivy_bound_and_the_deck_bound_are_different_questions() {
        assert_eq!(
            alloc_out(&[
                "let base = build 1000",
                "in let deck = deck-short-of (base + 1000) 100",
                "in let bivy = deck-bound-short-of (base + 1000) 100",
                "in print-line-uni (show deck & \" \" & show bivy)",
            ]),
            "False True"
        );
    }

    /// Thirteen builds per compile, each after a compact, must all land on the
    /// SAME base -- otherwise a later phase's deck sits above an earlier
    /// phase's ceiling and the guard fires on arithmetic alone.
    #[test]
    fn a_build_after_a_compact_reuses_the_same_base() {
        assert_eq!(
            alloc_pos(&[
                "let one = build 1000",
                "in let __a = pitch 200",
                "in let __b = phase-compact",
                "in let two = build 2000",
                "in let __c = phase-compact",
                "in let three = build 500",
                "in print-line-uni (show one & \" \" & show two & \" \" & show three)",
            ]),
            "0 0 0"
        );
    }

    /// WITHOUT the compact they do not, and that is the failure mode worth
    /// naming: the second reservation starts where the first ended, so a
    /// ceiling computed from the first is already behind the cursor and the
    /// guard fires on arithmetic rather than on usage.
    #[test]
    fn a_build_without_a_compact_climbs_and_the_first_ceiling_goes_stale() {
        assert_eq!(
            alloc_pos(&[
                "let one = build 1000",
                "in let two = build 1000",
                "in let stale = deck-short-of (one + 1000) 8",
                "in print-line-uni (show one & \" \" & show two & \" \" & show stale)",
            ]),
            "0 1000 True"
        );
    }

    /// **A LINKED LIST IS A MUTABLE HANDLE, and a `List` is not.**
    ///
    /// `__linked-list-push` is `list-push`, and every caller in the compiler
    /// rebinds what it answers -- which is why modelling it as a fresh `List`
    /// looked right. It is not: upstream pushes IN PLACE and answers the same
    /// handle, so a caller that keeps its own reference sees the push. The
    /// scoper does exactly that when it accumulates a chapter's definitions,
    /// and with a functional push the table came out EMPTY -- every name in
    /// every program undefined, down to a function's own parameter.
    ///
    /// `List` stays immutable, because Codex's is. `LinkedList` is a different
    /// type over there (`LinkedListTy`, not `list`) and it is a different type
    /// here.
    #[test]
    fn a_linked_list_push_is_seen_through_the_original_handle() {
        assert_eq!(
            alloc_out(&[
                "let ll = __linked-list-empty 0",
                "in let __a = __linked-list-push ll 1",
                "in let __b = __linked-list-push ll 2",
                "in let seen = __linked-list-to-list ll",
                "in print-line-uni (show (list-length seen) & \" \" & show seen)",
            ]),
            "2 [1, 2]"
        );
    }

    /// Two empty linked lists are two handles, so a push into one is not a push
    /// into the other.
    #[test]
    fn two_linked_lists_are_two_handles() {
        assert_eq!(
            alloc_out(&[
                "let a = __linked-list-empty 0",
                "in let b = __linked-list-empty 0",
                "in let __p = __linked-list-push a 1",
                "in print-line-uni (show (list-length (__linked-list-to-list a)) & \" \" & show (list-length (__linked-list-to-list b)))",
            ]),
            "1 0"
        );
    }

    // ---- the extent, and the one cursor --------------------------------
    //
    // `PhaseAllocator.codex` describes ONE allocation cursor, R10:
    //
    //   "R10 IS THE DECK CURSOR, BUT ONLY INSIDE AN EXTENT. `__deck-enter`
    //    copies the deck-pos cell into R10 and `__deck-exit` writes it back,
    //    on the zero crossings of the nesting counter, so within an extent
    //    every allocation moves R10 down the deck ... Outside an extent R10 is
    //    the bivy frontier."
    //
    // So `__heap-save` does not always answer the same thing, and that is what
    // makes `copy-sx-defs-guarded`'s `__heap-save >= ceiling` a sensible
    // question: inside the extent it asks whether the DECK cursor has reached
    // the reservation's top. Outside, the frontier parks ON that top the
    // instant `build` reserves, so the same test would be true immediately and
    // every guarded copy would saturate.

    /// Outside an extent the cursor is the bivy frontier, and advancing moves
    /// it.
    #[test]
    fn outside_an_extent_the_cursor_is_the_bivy() {
        assert_eq!(
            alloc_pos(&[
                "let a = __heap-save",
                "in let __x = __heap-advance 100",
                "in let b = __heap-save",
                "in print-line-uni (show a & \" \" & show b)",
            ]),
            "0 100"
        );
    }

    /// **INSIDE AN EXTENT IT IS THE DECK CURSOR**, loaded from the deck-pos
    /// cell on the way in. The bivy is left exactly where it was.
    #[test]
    fn inside_an_extent_the_cursor_is_the_deck() {
        assert_eq!(
            alloc_pos(&[
                "let base = build 1000",
                "in let outside = __heap-save",
                "in let __e = __deck-enter",
                "in let inside = __heap-save",
                "in let __a = __heap-advance 40",
                "in let moved = __heap-save",
                "in let __x = __deck-exit",
                "in let after = __heap-save",
                "in print-line-uni (show outside & \" \" & show inside & \" \" & show moved & \" \" & show after)",
            ]),
            "1000 0 40 1000"
        );
    }

    /// The write-back happens at the exit: the deck-pos cell holds where the
    /// cursor got to, which is what the phase's usage is measured from.
    #[test]
    fn the_exit_writes_the_cursor_back_to_the_cell() {
        assert_eq!(
            alloc_pos(&[
                "let base = build 1000",
                "in let before = __deck-pos",
                "in let __e = __deck-enter",
                "in let __a = __heap-advance 40",
                "in let during = __deck-pos",
                "in let __x = __deck-exit",
                "in let after = __deck-pos",
                "in print-line-uni (show before & \" \" & show during & \" \" & show after)",
            ]),
            "0 0 40"
        );
    }

    /// **ONLY THE ZERO CROSSINGS COUNT.** A nested extent neither reloads the
    /// cursor on the way in nor writes it back on the way out, so a phase-wide
    /// extent keeps the cell frozen at the base however many extents sit inside
    /// it -- which is exactly why `deck-short-of` asks about the floor's width
    /// and never about the usage.
    #[test]
    fn only_the_outermost_extent_copies_the_cell() {
        assert_eq!(
            alloc_pos(&[
                "let base = build 1000",
                "in let __e1 = __deck-enter",
                "in let __a1 = __heap-advance 10",
                "in let __e2 = __deck-enter",
                "in let __a2 = __heap-advance 10",
                "in let inner = __deck-pos",
                "in let __x2 = __deck-exit",
                "in let mid = __deck-pos",
                "in let __a3 = __heap-advance 10",
                "in let __x1 = __deck-exit",
                "in let outer = __deck-pos",
                "in print-line-uni (show inner & \" \" & show mid & \" \" & show outer)",
            ]),
            "0 0 30"
        );
    }

    /// `deck-record` IS the extent. The emitters compile it to
    /// `__deck-enter, the body, __deck-exit` -- its Codex definition is the
    /// identity only because the emitter never runs that body. This arm has to
    /// do the same, or nothing ever opens an extent and every guarded copy
    /// measures the bivy against a ceiling the bivy is already past.
    #[test]
    fn deck_record_opens_an_extent_around_its_argument() {
        assert_eq!(
            alloc_pos(&[
                "let base = build 1000",
                "in let bivy0 = __heap-save",
                "in let r = deck-record (pitch 40)",
                "in let bivy1 = __heap-save",
                "in let cell = __deck-pos",
                "in print-line-uni (show bivy0 & \" \" & show r & \" \" & show bivy1 & \" \" & show cell)",
            ]),
            "1000 0 1000 40"
        );
    }

    /// The allocator is arithmetic here: advance moves the position, restore
    /// puts it back, and `deck-short-of`'s two operands answer accordingly.
    #[test]
    fn the_heap_position_moves_and_comes_back() {
        let src = "Chapter: T\n\nSection: E\n\n  opening : [Console] Nothing = act\n                 let a = __heap-save\n    in let __x = __heap-advance 1000\n                 in let b = __heap-save\n    in let __y = __heap-restore a\n                 in let c = __heap-save\n                 in print-line-uni (show a & \" \" & show b & \" \" & show c)\n  end\n";
        assert_eq!(from_origin(out(src).trim().to_string()), "0 1000 0");
    }

    /// **`list-set-at` MUTATES IN PLACE**, and this is the upstream regression
    /// test `codex/plugs/wasm/test/list-set-at-rt.codex` transcribed. The wasm
    /// plug emitted it as a copy and row 8 of the plugs backlog records what
    /// that cost: every skip-list insert bumped `size` and linked nothing, so
    /// name resolution searched a 266-name scope that had no links in it.
    ///
    /// The compiler's `splice-new-node` DISCARDS both results:
    ///
    /// ```text
    /// in let dummy1 = list-set-at (pred.forward) i new-node
    /// in let dummy2 = list-set-at (pred.spans) i (new-pos - pred-rank)
    /// in splice-new-node s path new-node height new-pos (i + 1)
    /// ```
    ///
    /// so the links ARE the side effect and there is nothing else.
    #[test]
    fn a_discarded_list_set_at_is_still_visible() {
        let src = "Chapter: T\n\nSection: S\n\n  clobber : List Integer -> Integer\n  clobber (xs) =\n    let ignored = list-set-at xs 1 99\n    in 0\n\n  show-list : List Integer, Integer, Text -> Text\n  show-list (xs) (i) (acc) =\n    if i >= list-length xs then acc\n    else show-list xs (i + 1) (acc & \" \" & show (list-at xs i))\n\nSection: E\n\n  opening : [Console] Nothing = act\n                 let xs = [10, 20, 30]\n    in let d1 = clobber xs\n    in let ret = list-set-at xs 0 5\n                 in print-line-uni (show-list xs 0 \"\" & \" |\" & show-list ret 0 \"\")\n  end\n";
        assert_eq!(out(src).trim(), "5 99 30 | 5 99 30");
    }

    /// A list reached THROUGH A FIELD is the same list, so a write through the
    /// field is visible from the record. The skip list only ever reaches its
    /// backing that way -- `pred.forward`, `s.head.spans` -- so a `List` that
    /// copied on the way out of a field would defeat the fix above.
    #[test]
    fn a_write_through_a_field_reaches_the_records_list() {
        let src = "Chapter: T\n\nSection: S\n\n  Holder = record {\n    cells : List Integer\n  }\n\n  clobber-field : Holder -> Integer\n  clobber-field (h) =\n    let ignored = list-set-at (h.cells) 2 77\n    in 0\n\n  show-list : List Integer, Integer, Text -> Text\n  show-list (xs) (i) (acc) =\n    if i >= list-length xs then acc\n    else show-list xs (i + 1) (acc & \" \" & show (list-at xs i))\n\nSection: E\n\n  opening : [Console] Nothing = act\n                 let h = Holder { cells = [1, 2, 3] }\n    in let d2 = clobber-field h\n                 in print-line-uni (show-list (h.cells) 0 \"\")\n  end\n";
        assert_eq!(out(src).trim(), "1 2 77");
    }

    /// **A list LITERAL is a fresh list every time it is evaluated**, or the
    /// mutation above would leak between calls. `make-end-node`'s `forward =
    /// []` and `replicate-node`'s accumulator are both literals inside loops.
    #[test]
    fn a_list_literal_is_fresh_on_every_evaluation() {
        let src = "Chapter: T\n\nSection: S\n\n  fresh : Integer -> List Integer\n  fresh (n) = [n, n, n]\n\n  show-list : List Integer, Integer, Text -> Text\n  show-list (xs) (i) (acc) =\n    if i >= list-length xs then acc\n    else show-list xs (i + 1) (acc & \" \" & show (list-at xs i))\n\nSection: E\n\n  opening : [Console] Nothing = act\n                 let a = fresh 7\n    in let __x = list-set-at a 0 1\n    in let b = fresh 7\n                 in print-line-uni (show-list a 0 \"\" & \" |\" & show-list b 0 \"\")\n  end\n";
        assert_eq!(out(src).trim(), "1 7 7 | 7 7 7");
    }

    /// **`list-push` WRITES THROUGH TOO, and `&` allocates.** The two halves
    /// are not a symmetry and each is somebody's prelude, read rather than
    /// reasoned about:
    ///
    /// ```text
    /// fn cx_ll_push(l: anytype, v: anytype) @TypeOf(l) {
    ///     l.items.append(cx_gpa, v) catch @panic("oom");
    ///     return l;
    /// }
    /// fn cx_ll_concat(a: anytype, b: @TypeOf(a)) @TypeOf(a) {
    ///     const c = cx_new(...);  // a FRESH list, both sides copied in
    /// ```
    ///
    /// `cx_ll_cons` allocates like concat, `cx_ll_insert_at` writes through
    /// like push. The wasm plug reaches the same place from the other side: a
    /// push is in place when the capacity is there and copies when it is not,
    /// which is exactly why `__list-with-capacity` exists and why its capacity
    /// is documented upstream as load-bearing rather than a hint.
    ///
    /// **This was pinned the WRONG WAY ROUND first** -- push allocating, on
    /// the reasoning that an aliasing accumulator is a footgun -- and the
    /// compiler said otherwise within the hour. `tail-resolve-binding-chunk`
    /// pushes into a `__list-with-capacity` chunk, DISCARDS every result, and
    /// answers a count its caller uses to read the chunk back.
    #[test]
    fn a_push_writes_through_and_an_append_allocates() {
        let src = "Chapter: T\n\nSection: S\n\n  show-list : List Integer, Integer, Text -> Text\n  show-list (xs) (i) (acc) =\n    if i >= list-length xs then acc\n    else show-list xs (i + 1) (acc & \" \" & show (list-at xs i))\n\nSection: E\n\n  opening : [Console] Nothing = act\n                 let a = [1, 2]\n    in let c = a & [9]\n    in let __p = list-push a 3\n    in let __q = list-push c 8\n                 in print-line-uni (show-list a 0 \"\" & \" |\" & show-list c 0 \"\")\n  end\n";
        assert_eq!(out(src).trim(), "1 2 3 | 1 2 9 8");
    }

    /// **THE CHUNK PATTERN, which is the shape that found it.** A caller fills
    /// a capacity list, throws away what every push answered, and reports how
    /// many it did; the caller then reads the list it passed IN. Reduced from
    /// `tail-resolve-binding-chunk` and `tail-copy-binding-chunk`, which is
    /// how the type checker resolves bindings in budget-sized batches.
    #[test]
    fn a_discarded_push_is_visible_to_the_caller_that_passed_the_list() {
        let src = "Chapter: T\n\nSection: S\n\n  fill : List Integer, Integer, Integer -> Integer\n  fill (chunk) (i) (n) =\n    if i >= n then n\n    else let discarded = list-push chunk (i * 10)\n    in fill chunk (i + 1) n\n\n  show-list : List Integer, Integer, Text -> Text\n  show-list (xs) (i) (acc) =\n    if i >= list-length xs then acc\n    else show-list xs (i + 1) (acc & \" \" & show (list-at xs i))\n\nSection: E\n\n  opening : [Console] Nothing = act\n                 let chunk = __list-with-capacity 4\n    in let n = fill chunk 0 3\n                 in print-line-uni (show n & \" |\" & show-list chunk 0 \"\")\n  end\n";
        assert_eq!(out(src).trim(), "3 | 0 10 20");
    }

    // -- the flat memory ---------------------------------------------------
    //
    // The contract is the zig plug's prelude, which is a fixed point against
    // bare metal: one byte-addressed region starting at 0, little-endian
    // throughout, unsigned loads below 8 bytes and a raw bit pattern at 8,
    // truncating stores, and a `poke-*` that answers 0. See
    // `ZigEmitter.codex:4150`ff and `WasmEmitter.codex:1873`ff, which agree.

    /// A byte comes back as it went in, and memory that was never written
    /// reads as zero rather than as an error -- `cx_buf_want` grows the region
    /// and the growth is zeroed.
    #[test]
    fn a_written_byte_reads_back_and_the_rest_is_zero() {
        let src = mem_body(
            "let a = __heap-save\n    in let __x = __heap-advance 64\n    in let __y = poke-byte a 3 200\n                 in print-line-uni (show (peek-byte a 3) & \" \" & show (peek-byte a 4) & \" \" & show (peek-byte a 0))",
        );
        assert_eq!(out(&src).trim(), "200 0 0");
    }

    /// **THE OFFSET IS PART OF THE ADDRESS.** Every one of these takes a base
    /// and an offset and adds them, which is why `memo-probe-at` can say
    /// `peek-32 slot 0` with the arithmetic already done.
    #[test]
    fn the_offset_and_the_base_are_added() {
        let src = mem_body(
            "let a = __heap-save\n    in let __x = __heap-advance 64\n    in let __y = poke-byte a 7 42\n                 in print-line-uni (show (peek-byte (a + 7) 0) & \" \" & show (peek-byte (a + 3) 4))",
        );
        assert_eq!(out(&src).trim(), "42 42");
    }

    /// **LITTLE-ENDIAN, and a 32-bit load CLEARS THE TOP HALF.** `cx_peek_32`
    /// rebuilds the value from byte 3 down with checked arithmetic, so it
    /// cannot answer anything negative; `memo-slot-key`'s `bit-and ... 
    /// 4294967295` is belt and braces over a load that is already unsigned.
    #[test]
    fn a_32_bit_load_is_little_endian_and_unsigned() {
        let src = mem_body(
            "let a = __heap-save\n    in let __x = __heap-advance 64\n    in let __1 = poke-byte a 0 1\n    in let __2 = poke-byte a 1 2\n    in let __3 = poke-byte a 2 3\n    in let __4 = poke-byte a 3 4\n    in let __f = poke-32 (a + 8) 0 4294967295\n                 in print-line-uni (show (peek-32 a 0) & \" \" & show (peek-32 (a + 8) 0))",
        );
        assert_eq!(out(&src).trim(), "67305985 4294967295");
    }

    /// **A QWORD LOAD IS THE RAW BIT PATTERN AND MAY BE NEGATIVE**, which is
    /// why `cx_peek_qword` rebuilds it with WRAPPING `*%` and `+%` where
    /// `cx_peek_32` uses checked arithmetic. This number is not derived here:
    /// it is the measurement in that function's own comment, taken on bare
    /// metal on 2026-08-21 with `findings/probe-peek-qword.codex`, for the
    /// bytes `00 00 00 00 00 00 00 FF`.
    #[test]
    fn a_qword_load_carries_the_sign_bit() {
        let src = mem_body(
            "let a = __heap-save\n    in let __x = __heap-advance 64\n    in let __y = poke-byte a 7 255\n                 in print-line-uni (show (peek-qword a 0))",
        );
        assert_eq!(out(&src).trim(), "-72057594037927936");
    }

    /// A store keeps the low bytes and drops the rest, and it touches no byte
    /// beyond its width.
    #[test]
    fn a_store_truncates_and_stays_inside_its_width() {
        let src = mem_body(
            "let a = __heap-save\n    in let __x = __heap-advance 64\n    in let __y = poke-32 a 0 (4294967296 + 305419896)\n                 in print-line-uni (show (peek-32 a 0) & \" \" & show (peek-byte a 4) & \" \" & show (peek-qword a 0))",
        );
        assert_eq!(out(&src).trim(), "305419896 0 305419896");
    }

    /// **A POKE ANSWERS 0**, in every plug, so a `let` that binds one is
    /// binding a constant and the write is the whole of what it did.
    #[test]
    fn a_poke_answers_zero() {
        let src = mem_body(
            "let a = __heap-save\n    in let __x = __heap-advance 64\n                 in print-line-uni (show (poke-byte a 0 7) & \" \" & show (poke-32 a 8 7) & \" \" & show (poke-qword a 16 7))",
        );
        assert_eq!(out(&src).trim(), "0 0 0");
    }

    /// `__memset` fills exactly n bytes and answers nothing. The checker opens
    /// every batch by zeroing its cons table this way -- `check-batch-open`
    /// does it twice -- so a memset that ran short would leave a probe reading
    /// a key from the last compile.
    #[test]
    fn a_memset_fills_exactly_its_range() {
        let src = mem_body(
            "let a = __heap-save\n    in let __x = __heap-advance 64\n    in let __1 = poke-byte a 0 9\n    in let __2 = poke-byte a 3 9\n    in let __3 = poke-byte a 4 9\n    in let __z = __memset a 0 4\n                 in print-line-uni (show (peek-byte a 0) & \" \" & show (peek-byte a 3) & \" \" & show (peek-byte a 4))",
        );
        assert_eq!(out(&src).trim(), "0 0 9");
    }

    /// A memset writes the LOW BYTE of its value, not the value.
    #[test]
    fn a_memset_writes_one_byte_of_its_argument() {
        let src = mem_body(
            "let a = __heap-save\n    in let __x = __heap-advance 64\n    in let __z = __memset a 513 2\n                 in print-line-uni (show (peek-byte a 0) & \" \" & show (peek-byte a 1) & \" \" & show (peek-byte a 2))",
        );
        assert_eq!(out(&src).trim(), "1 1 0");
    }

    /// **THE ALLOCATOR AND THE MEMORY ARE THE SAME ADDRESSES.** This is the
    /// join that makes the whole thing a model rather than two: the checker
    /// takes its memo table's base from `__heap-save`, advances past it, and
    /// pokes into what it reserved. Two reservations must not overlap.
    #[test]
    fn two_reservations_do_not_overlap() {
        let src = mem_body(
            "let a = __heap-save\n    in let __x = __heap-advance 16\n    in let b = __heap-save\n    in let __y = __heap-advance 16\n    in let __1 = poke-qword a 0 111\n    in let __2 = poke-qword b 0 222\n                 in print-line-uni (show (b - a) & \" \" & show (peek-qword a 0) & \" \" & show (peek-qword b 0))",
        );
        assert_eq!(out(&src).trim(), "16 111 222");
    }

    /// **A DECIMAL LITERAL IS CORRECTLY ROUNDED HERE AND IS NOT UPSTREAM.**
    /// 0.1 and 1e300 are inside the fifteen significant digits upstream gets
    /// right, so those two agree with every arm. `9007199254740993` is 2^53+1
    /// and is the shape issue 125 is about; what is pinned is the CORRECT
    /// answer, which is 2^53 as a double, and a disagreement with the bank
    /// there is this arm being right.
    #[test]
    fn a_real_literal_is_correctly_rounded() {
        let src = mem_body(
            "print-line-uni (show (text-to-double-bits \"0.1\") & \" \" & show (text-to-double-bits \"1e300\") & \" \" & show (text-to-double-bits \"9007199254740993.0\"))",
        );
        assert_eq!(
            out(&src).trim(),
            format!(
                "{} {} {}",
                0.1f64.to_bits() as i64,
                1e300f64.to_bits() as i64,
                9007199254740992.0f64.to_bits() as i64
            )
        );
    }

    /// **`__self-type-defs` IS EMPTY**, which is what both plugs answer and
    /// therefore what this arm must. It is not zero-arity by accident either:
    /// the arity table had to know, or the call reads as one argument short.
    #[test]
    fn the_self_type_table_is_empty_in_a_hosted_compiler() {
        let src = mem_body("print-line-uni (show (list-length __self-type-defs))");
        assert_eq!(out(&src).trim(), "0");
    }

    /// **THE DURABILITY TEST, WHICH IS THE WHOLE REASON A TEXT HAS AN
    /// ADDRESS.** The compiler asks
    ///
    /// ```text
    /// copy-sx-text (b) (t) = if address-of t < b then t else substring t 0 (text-length t)
    /// ```
    ///
    /// and answers "rebuild it" whenever that is false. With a host pointer it
    /// was false for every text, always, and the source of a 112 KB subject
    /// was rebuilt at every keep boundary -- 2.3 GB of a 2.3 GB peak. This
    /// pins the two halves of the answer: a text made BEFORE a base compares
    /// below it, and one made AFTER does not.
    ///
    /// A LITERAL IS BELOW EVERY BASE, which is the other half. It lives in the
    /// image band under the heap origin, so it is durable against a base taken
    /// at any point in the run -- which is what makes sharing it correct
    /// rather than lucky.
    #[test]
    fn a_text_is_durable_against_a_base_taken_after_it() {
        let src = mem_body(
            "let lit = \"a literal, which lives in the image\"\n    in let early = \"made\" & \" early\"\n    in let b = __heap-save\n    in let late = \"made\" & \" late\"\n                 in print-line-uni (show (address-of lit < b) & \" \" & show (address-of early < b) & \" \" & show (address-of late < b))",
        );
        assert_eq!(out(&src).trim(), "True True False");
    }

    /// Two texts are two addresses, or every content key in the checker's cons
    /// table collides -- which is exactly the defect this arm found in the zig
    /// plug, where `.rodata` answered 0 for all of them.
    #[test]
    fn two_texts_have_two_addresses() {
        let src = mem_body(
            "let a = \"Console\" & \".Write\"\n    in let b = \"Device\" & \".Mmio\"\n                 in print-line-uni (show (address-of a == address-of b) & \" \" & show (address-of a == 0))",
        );
        assert_eq!(out(&src).trim(), "False False");
    }

    /// **A QWORD MAY STRADDLE A PAGE**, and the flat memory is paged. Nothing
    /// in the compiler aligns its memo slots to a page -- `table + idx * 16`
    /// lands wherever the reservation put it -- so an eight-byte load four
    /// bytes before a boundary is an ordinary case and not an edge one.
    /// Written before the page lookup was hoisted out of the byte loop,
    /// because that is exactly the change that would break it.
    #[test]
    fn a_load_and_a_store_may_cross_a_page() {
        let src = mem_body(
            "let a = __heap-save\n    in let __x = __heap-advance 16384\n    in let __y = poke-qword (a + 4092) 0 (0 - 72057594037927936)\n    in let __z = poke-32 (a + 8190) 0 4294967295\n                 in print-line-uni (show (peek-qword (a + 4092) 0) & \" \" & show (peek-byte (a + 4099) 0) & \" \" & show (peek-32 (a + 8190) 0) & \" \" & show (peek-byte (a + 8194) 0))",
        );
        assert_eq!(out(&src).trim(), "-72057594037927936 255 4294967295 0");
    }

    /// A read of a page nobody wrote answers zero and maps NOTHING. The driver
    /// opens with `__heap-advance 536870912`; half a gigabyte of pages for a
    /// region nobody touches would be the whole of the memory this arm has.
    #[test]
    fn reading_unmapped_memory_maps_nothing() {
        let src = mem_body(
            "let a = __heap-save\n    in let __x = __heap-advance 536870912\n                 in print-line-uni (show (peek-qword (a + 400000000) 0) & \" \" & show (peek-byte (a + 12345678) 0))",
        );
        assert_eq!(out(&src).trim(), "0 0");
    }

    /// **A FILE COMES BACK WHOLE**, which is the only reason this builtin
    /// exists here: the harness that drives a compile reads its subject with
    /// `src <- read-file-uni "/dev/stdin"`, and without it a subject has to be
    /// inlined as a Text literal -- which put the compiler in its own unit
    /// TWICE and took the input to 6.9 MB, past the size the zig arm survives.
    #[test]
    fn a_file_comes_back_whole() {
        let path = std::env::temp_dir().join("codexrun-read-test.txt");
        let body = "Chapter: T\n  a line\n  and a \"quoted\" one\n";
        std::fs::write(&path, body).unwrap();
        let src = mem_body(&format!(
            "let t = read-file-uni \"{}\"\n                 in print-line-uni (show (text-length t) & \" \" & show (text-contains t \"quoted\"))",
            path.display()
        ));
        assert_eq!(out(&src).trim(), format!("{} True", body.len()));
        std::fs::remove_file(&path).ok();
    }

    /// **A FILE THAT IS NOT THERE IS AN ERROR, NOT AN EMPTY TEXT.** The zig
    /// plug panics -- `cx_read_file_uni: cannot open` -- and a silent empty
    /// string would be a compile of nothing that reports success, which is the
    /// exact shape of a green run that never ran.
    #[test]
    fn a_missing_file_is_refused_rather_than_empty() {
        let src = mem_body(
            "let t = read-file-uni \"/no/such/file/at/all\"\n                 in print-line-uni (show (text-length t))",
        );
        let e = std::panic::catch_unwind(|| out(&src));
        assert!(e.is_err(), "a missing file must not read as an empty text");
    }

    /// Wrap a body in the smallest chapter that can hold it.
    fn mem_body(body: &str) -> String {
        format!("Chapter: T\n\nSection: E\n\n  opening : [Console] Nothing = act\n                 {body}\n  end\n")
    }

    /// **A NULLARY THAT ANSWERS A LIST CANNOT BE CACHED once anything in the
    /// program writes**, and `skip-list-text-empty` is the definition that
    /// proved it. It mentions no impure builtin and calls nothing impure, so
    /// the call-graph fixpoint leaves it cacheable -- and every
    /// `skip-list-text-insert` splices into the head node's `forward` list it
    /// handed out. Two skip lists then share one accumulator: the second
    /// insert of `b` went missing and `x` was unfindable in a list of size 1.
    #[test]
    fn a_list_valued_nullary_is_rebuilt_when_the_program_writes() {
        let src = "Chapter: T\n\nSection: S\n\n  seed : List Integer\n  seed = [1, 2, 3]\n\n  show-list : List Integer, Integer, Text -> Text\n  show-list (xs) (i) (acc) =\n    if i >= list-length xs then acc\n    else show-list xs (i + 1) (acc & \" \" & show (list-at xs i))\n\nSection: E\n\n  opening : [Console] Nothing = act\n                 let a = seed\n    in let __x = list-set-at a 0 99\n                 in print-line-uni (show-list a 0 \"\" & \" |\" & show-list seed 0 \"\")\n  end\n";
        assert_eq!(out(src).trim(), "99 2 3 | 1 2 3");
    }

    /// **And it IS still cached when nothing writes**, which is what keeps
    /// safari's route tables off the rebuild path. The same shape without a
    /// `list-set-at` anywhere hands out one object, so `address-of` agrees
    /// with itself across two mentions.
    #[test]
    fn a_list_valued_nullary_is_shared_when_nothing_writes() {
        let src = "Chapter: T\n\nSection: S\n\n  seed : List Integer\n  seed = [1, 2, 3]\n\nSection: E\n\n  opening : [Console] Nothing = act\n                 print-line-uni (show (address-of seed == address-of seed))\n  end\n";
        assert_eq!(out(src).trim(), "True");
    }

    /// **The skip list is the thing this was found in**, so it is the thing
    /// pinned: an insert must be FINDABLE, not merely counted. This is
    /// `skip-list-text`'s shape reduced to what carries the defect -- a node
    /// whose forward pointer is written through a discarded `list-set-at`.
    #[test]
    fn a_spliced_node_is_reachable_from_its_predecessor() {
        let src = "Chapter: T\n\nSection: S\n\n  Node = record {\n    value : Text,\n    forward : List Node\n  }\n\n  end-node : Node\n  end-node = Node { value = \"\", forward = [] }\n\n  splice : Node, Node -> Integer\n  splice (pred) (fresh) =\n    let dummy = list-set-at (pred.forward) 0 fresh\n    in 0\n\nSection: E\n\n  opening : [Console] Nothing = act\n                 let head = Node { value = \"h\", forward = [end-node] }\n    in let n = Node { value = \"x\", forward = [end-node] }\n    in let d = splice head n\n                 in print-line-uni ((list-at (head.forward) 0).value)\n  end\n";
        assert_eq!(out(src).trim(), "x");
    }
}

/// Does anything in this program WRITE?
///
/// The gate in front of `frozen`, and the reason safari does not pay for the
/// compiler's problem: 54 spec chapters contain no `list-set-at`, no
/// `__record-set` and no field assignment between them, so no cached value
/// there can be reached by a writer and all of them may be shared. Narrowing
/// the cache unconditionally cost that suite 1.7x for a hazard it does not
/// have.
///
/// Wrong in the safe direction costs a rebuild; wrong in the other loses an
/// update. So this looks for the writers by name and takes any mention as a
/// write, without asking what is written.
fn program_writes(
    syms: &SymTab,
    consts: &[&crate::ast::Def],
    funs: &[(u32, &crate::ast::Def)],
) -> bool {
    let writers: Vec<Sym> =
        ["list-set-at", "__record-set"].iter().filter_map(|n| syms.find(n)).collect();
    let mut found = false;
    for d in consts.iter().copied().chain(funs.iter().map(|(_, d)| *d)) {
        d.body.walk(&mut |x| match x {
            crate::ast::Expr::NameRef(n, _) => found |= writers.contains(n),
            crate::ast::Expr::FieldAssign(..) => found = true,
            _ => {}
        });
    }
    found
}

/// **A CACHED NULLARY HANDS OUT ONE OBJECT, so it may only hold values nobody
/// can write to.** `skip-list-text-empty` is the definition that proves it: it
/// mentions no impure builtin and calls nothing impure, so the call-graph
/// fixpoint below leaves it cacheable -- and it answers a record whose head
/// node's `forward` list every later `skip-list-text-insert` splices into. One
/// shared empty list is then the accumulator for every skip list in the
/// program.
///
/// This is a look at the VALUE and not at the body, because the body is not
/// where the aliasing is: the writer is somebody else's code, reached through
/// a handle this definition gave away. A `List` or a `Record` is writable, a
/// scalar is not, and a constructor is exactly as writable as its fields.
fn frozen(v: &Value) -> bool {
    match v {
        Value::Int(_)
        | Value::Real(_)
        | Value::Text(_)
        | Value::Char(_)
        | Value::Bool(_)
        | Value::Unit => true,
        Value::Ctor(_, fs) => fs.iter().all(frozen),
        Value::List(_) | Value::Record(..) | Value::Fun(_) => false,
    }
}

/// The builtins that READ OR WRITE the allocator's two positions, plus the one
/// that mutates a record.
///
/// Nothing in a type says these are impure -- their declared rows are `empty`,
/// because upstream's effect system is about capabilities and not about the
/// bump allocator underneath everything.
const IMPURE_BUILTINS: &[&str] = &[
    "__heap-save",
    "__heap-restore",
    "__heap-advance",
    "__deck-pos",
    "__deck-set",
    "__deck-enter",
    "__deck-exit",
    "__record-set",
    // The flat memory, both ways. A poke is obviously a write; a PEEK has to
    // be here too, because a cached nullary that reads memory keeps whatever
    // the region held the first time anybody asked. Upstream says the same
    // thing in its own table -- every one of these carries `bs-varies = True`.
    "peek-byte",
    "peek-16",
    "peek-32",
    "peek-qword",
    "poke-byte",
    "poke-16",
    "poke-32",
    "poke-qword",
    "poke-mmio",
    "poke-mmio-32",
    "__memset",
];

/// Every definition that can touch mutable state, directly or through a call.
///
/// **THE EFFECT ROW IS NOT ENOUGH TO DECIDE WHAT MAY BE CACHED, and a test
/// found it.** `phase-compact : Nothing = __heap-restore (__deck-pos)` is a
/// NULLARY whose declared type carries no effect, so the cache kept its first
/// answer and every later mention did nothing at all. The compiler calls it
/// between phases to drop the bivy back to the deck; cached, the second phase's
/// reservation started where the first ended, and a ceiling computed from the
/// first was already behind the cursor -- CDX9002, deck overflow, on
/// arithmetic rather than on usage.
///
/// So this is a fixpoint over the call graph rather than a look at one body: a
/// definition is impure if it mentions an impure builtin, or a field
/// assignment, or the name of anything already known to be impure. It runs once
/// at startup and it only ever REMOVES definitions from the cache, so being
/// wrong in this direction costs a rebuild and being wrong in the other loses
/// an update.
///
/// Names, not chapter-qualified keys, so two definitions sharing a name are
/// both marked. Over-approximating is the safe side here.
fn impure_names(
    syms: &SymTab,
    consts: &[&crate::ast::Def],
    funs: &[(u32, &crate::ast::Def)],
) -> std::collections::HashSet<Sym> {
    use std::collections::{HashMap, HashSet};
    let mut impure: HashSet<Sym> = HashSet::new();
    for b in IMPURE_BUILTINS {
        if let Some(s) = syms.find(b) {
            impure.insert(s);
        }
    }
    // What each definition mentions, and whether it assigns to a field itself.
    let mut mentions: HashMap<Sym, HashSet<Sym>> = HashMap::new();
    let mut seeds: Vec<Sym> = Vec::new();
    let all = consts.iter().copied().chain(funs.iter().map(|(_, d)| *d));
    for d in all {
        let e = mentions.entry(d.name).or_default();
        d.body.walk(&mut |x| match x {
            crate::ast::Expr::NameRef(n, _) => {
                e.insert(*n);
            }
            crate::ast::Expr::FieldAssign(..) => seeds.push(d.name),
            _ => {}
        });
    }
    impure.extend(seeds);
    // Fixpoint. The graph is small and shallow; this settles in a few passes.
    loop {
        let mut grew = false;
        for (name, refs) in &mentions {
            if impure.contains(name) {
                continue;
            }
            if refs.iter().any(|r| impure.contains(r)) {
                impure.insert(*name);
                grew = true;
            }
        }
        if !grew {
            return impure;
        }
    }
}

/// Does this type carry an effect row anywhere inside it?
///
/// Recursive rather than a look at the head, because `[Console] Nothing` is the
/// shape that matters here but an effect can sit under a `Forall` or to the
/// right of an arrow, and a nullary whose type says it performs anything must
/// not be cached. Wrong in the safe direction costs a rebuild; wrong in the
/// other direction silently drops an effect.
fn mentions_effect(t: &TypeExpr) -> bool {
    match t {
        TypeExpr::Effect(..) => true,
        TypeExpr::Named(..) => false,
        TypeExpr::Fun(a, b, _) => mentions_effect(a) || mentions_effect(b),
        TypeExpr::App(h, args, _) => mentions_effect(h) || args.iter().any(mentions_effect),
        TypeExpr::BoundedInt(a, ..) => mentions_effect(a),
        TypeExpr::PropEq(a, b, _) => mentions_effect(a) || mentions_effect(b),
        TypeExpr::Constrained(_, _, a, _) => mentions_effect(a),
        TypeExpr::Linear(a, _) => mentions_effect(a),
        TypeExpr::Forall(_, a, b, _) => mentions_effect(a) || mentions_effect(b),
    }
}
