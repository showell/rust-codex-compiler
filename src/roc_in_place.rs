//! **WHERE CODEX'S IN-PLACE LIST WRITES AND ROC'S VALUE LISTS PART.** Codex's
//! `list-set-at` writes the list it is handed, so everything holding that
//! list sees the write; Roc's `List.set` answers a new list, and every other
//! holder keeps the old one. The two agree when the program goes on reading
//! the list only through each write's answer. rocemit refuses the
//! definitions for which this module cannot show that:
//!
//! - one that writes a list parameter and does not answer it on every path
//!   (`Analysis::carry`), since its caller goes on with the list it passed;
//! - one that binds the answer of a `list-set-at` to a name nothing reads,
//!   since that write is seen only in place.
//!
//! A caller that keeps reading its own name for a list after handing it to a
//! writer is not checked here; tests/ladder.sh names such units DIVERGES.
//!
//! The verdicts that pin the refusals are codex/test's `edalias` and
//! `cryptobig` (the foreword's `cb-shl1-step` doubles a bignum in place and
//! answers the carry, and its caller reads the doubled list), which answer
//! wrong numbers when emitted without them.

use crate::ir_chapter::{IrActStmt, IrDef, IrExpr};
use crate::symbol::{Sym, SymTab};
use std::collections::{BTreeMap, BTreeSet};

/// The refusal for each definition whose in-place writes Roc cannot follow.
pub fn refusals(defs: &[IrDef], syms: &SymTab) -> BTreeMap<Sym, String> {
    let a = Analysis { syms, by_name: defs.iter().map(|d| (d.name, d)).collect() };
    let writers = a.writers(defs);
    let carriers = a.carriers(&writers);
    let mut out = BTreeMap::new();
    for d in defs {
        let lost = (0..d.params.len()).find(|q| !carriers.contains_key(&(d.name, *q)) && a.writes_directly(d, *q));
        if let Some(q) = lost {
            out.insert(
                d.name,
                format!(
                    "`{}` writes its list parameter `{}` and does not answer it on every path",
                    syms.text(d.name),
                    syms.text(d.params[q].name)
                ),
            );
        } else if a.drops_a_write(&d.body) {
            out.insert(
                d.name,
                format!("`{}` drops the answer of a `list-set-at`, so the write is seen only in place", syms.text(d.name)),
            );
        }
    }
    out
}

/// How a definition hands a written list parameter back.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Carry {
    /// Not known yet: where the fixed point starts, so a recursive definition
    /// may lean on itself. It merges as the identity.
    Unknown,
    /// The answer is the list.
    Whole,
    /// The answer is a record holding the list in this field.
    Field(String),
    /// The answer holds the list somewhere a caller cannot name.
    Opaque,
}

fn merge(a: Carry, b: Carry) -> Carry {
    match (a, b) {
        (Carry::Unknown, x) | (x, Carry::Unknown) => x,
        (x, y) if x == y => x,
        _ => Carry::Opaque,
    }
}

/// What holds the current version of the list being followed: a name, or a
/// field of a record a name is bound to.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Holder {
    Name(Sym),
    Field(Sym, String),
}

/// Each definition's parameters it writes in place, by position.
type Writers = BTreeMap<Sym, BTreeSet<usize>>;
/// Each written parameter its definition hands back, and how.
type Carriers = BTreeMap<(Sym, usize), Carry>;

struct Analysis<'a> {
    syms: &'a SymTab,
    by_name: BTreeMap<Sym, &'a IrDef>,
}

impl Analysis<'_> {
    fn text(&self, n: Sym) -> &str {
        self.syms.text(n)
    }

    /// Each definition's parameters it writes: a `list-set-at` on the
    /// parameter or a name bound to it, or one of those handed to a position
    /// another definition writes. Writers call writers, so this is a fixed
    /// point.
    fn writers(&self, defs: &[IrDef]) -> Writers {
        let mut followed = Vec::new();
        for d in defs {
            for (q, p) in d.params.iter().enumerate() {
                followed.push((d, q, self.aliases(&d.body, p.name)));
            }
        }
        let mut writers = Writers::new();
        loop {
            let mut grew = false;
            for (d, q, cur) in &followed {
                if !writers.get(&d.name).is_some_and(|qs| qs.contains(q)) && self.writes(&d.body, cur, &writers, None) {
                    writers.entry(d.name).or_default().insert(*q);
                    grew = true;
                }
            }
            if !grew {
                return writers;
            }
        }
    }

    /// Whether `d` writes parameter `q` with a `list-set-at` of its own.
    fn writes_directly(&self, d: &IrDef, q: usize) -> bool {
        self.writes(&d.body, &self.aliases(&d.body, d.params[q].name), &Writers::new(), None)
    }

    /// The written parameters each definition hands back, and how: the
    /// largest assignment in which every body's `carry` agrees with it. A
    /// recursive writer starts `Unknown` and settles once its other paths
    /// are seen; a value only ever moves toward refusal, and the round cap
    /// refuses whatever has not settled.
    fn carriers(&self, writers: &Writers) -> Carriers {
        let mut carriers: Carriers =
            writers.iter().flat_map(|(n, qs)| qs.iter().map(move |q| ((*n, *q), Carry::Unknown))).collect();
        for _ in 0..carriers.len() + 8 {
            let mut changed = false;
            let keys: Vec<(Sym, usize)> = carriers.keys().copied().collect();
            for (n, q) in keys {
                let d = self.by_name[&n];
                match self.carry(&d.body, &[Holder::Name(d.params[q].name)], writers, &carriers) {
                    None => {
                        carriers.remove(&(n, q));
                        changed = true;
                    }
                    Some(c) if carriers.get(&(n, q)) != Some(&c) => {
                        carriers.insert((n, q), c);
                        changed = true;
                    }
                    _ => {}
                }
            }
            if !changed {
                return carriers;
            }
        }
        carriers.retain(|_, c| *c != Carry::Unknown);
        carriers
    }

    /// The names in a body that are the list `p` names: `p`, and every let
    /// bound to one of them or to a write of one.
    fn aliases(&self, body: &IrExpr, p: Sym) -> Vec<Holder> {
        let mut cur = vec![Holder::Name(p)];
        loop {
            let before = cur.len();
            body.walk(&mut |x| {
                if let IrExpr::Let(n, _, v, _, _) = x {
                    if !cur.contains(&Holder::Name(*n)) && self.is_alias(v, &cur, None) {
                        cur.push(Holder::Name(*n));
                    }
                }
            });
            if cur.len() == before {
                return cur;
            }
        }
    }

    /// Whether `e` is the list `cur` holds: a holder, a `list-set-at` or
    /// `list-push` on it (whose answer in Codex is the list it was handed),
    /// or, once carriers are known, a call handing it to a position whose
    /// callee answers it whole.
    fn is_alias(&self, e: &IrExpr, cur: &[Holder], carriers: Option<&Carriers>) -> bool {
        match e {
            IrExpr::Name(n, _, _) => cur.contains(&Holder::Name(*n)),
            IrExpr::FieldAccess(r, slot, _, _) => match &**r {
                IrExpr::Name(n, _, _) => cur.contains(&Holder::Field(*n, field_name(slot).to_string())),
                _ => false,
            },
            IrExpr::Apply(..) => {
                let (head, args) = call_spine(e);
                let IrExpr::Name(n, _, _) = head else { return false };
                match self.text(*n) {
                    "list-set-at" => args.len() == 3 && self.is_alias(args[0], cur, carriers),
                    "list-push" => args.len() == 2 && self.is_alias(args[0], cur, carriers),
                    _ => carriers.is_some_and(|cs| {
                        matches!(self.carried_arg(*n, &args, cur, cs), Some(Carry::Whole | Carry::Unknown))
                    }),
                }
            }
            _ => false,
        }
    }

    /// How a saturated call to `n` hands back the list `cur` holds, when one
    /// of its arguments is that list.
    fn carried_arg(&self, n: Sym, args: &[&IrExpr], cur: &[Holder], carriers: &Carriers) -> Option<Carry> {
        let d = self.by_name.get(&n)?;
        if args.len() != d.params.len() {
            return None;
        }
        args.iter()
            .enumerate()
            .find_map(|(q, a)| if self.is_alias(a, cur, Some(carriers)) { carriers.get(&(n, q)).cloned() } else { None })
    }

    /// Whether `e` writes the list `cur` holds: a `list-set-at` on it, or a
    /// call handing it to a position its callee writes.
    fn writes(&self, e: &IrExpr, cur: &[Holder], writers: &Writers, carriers: Option<&Carriers>) -> bool {
        let mut hit = false;
        e.walk(&mut |x| {
            if hit || !matches!(x, IrExpr::Apply(..)) {
                return;
            }
            let (head, args) = call_spine(x);
            let IrExpr::Name(n, _, _) = head else { return };
            hit = if self.text(*n) == "list-set-at" {
                args.len() == 3 && self.is_alias(args[0], cur, carriers)
            } else {
                writers
                    .get(n)
                    .is_some_and(|qs| qs.iter().any(|q| args.get(*q).is_some_and(|a| self.is_alias(a, cur, carriers))))
            };
        });
        hit
    }

    /// How every path through `e` answers the current version of the list
    /// `cur` holds, or `None` when some path does not. A let bound to the list
    /// or to a write of it moves the current version to the new name; a let
    /// bound to a call that answers a record holding it moves it to that
    /// field; a write anywhere else (a condition, an argument its callee does
    /// not hand back) leaves nothing holding it.
    fn carry(&self, e: &IrExpr, cur: &[Holder], writers: &Writers, carriers: &Carriers) -> Option<Carry> {
        use IrExpr as E;
        let cs = Some(carriers);
        match e {
            E::Let(n, _, v, body, _) => {
                let next = if self.is_alias(v, cur, cs) {
                    if matches!(**v, E::Name(..) | E::FieldAccess(..)) {
                        let mut more = cur.to_vec();
                        more.push(Holder::Name(*n));
                        more
                    } else {
                        vec![Holder::Name(*n)]
                    }
                } else if let Some(Carry::Field(f)) = self.carried_call(v, cur, carriers) {
                    vec![Holder::Field(*n, f)]
                } else if self.writes(v, cur, writers, cs) {
                    Vec::new()
                } else {
                    cur.to_vec()
                };
                self.carry(body, &next, writers, carriers)
            }
            E::If(c, t, f, _, _) => {
                if self.writes(c, cur, writers, cs) {
                    return None;
                }
                Some(merge(self.carry(t, cur, writers, carriers)?, self.carry(f, cur, writers, carriers)?))
            }
            E::Match(s, bs, _, _) => {
                if self.writes(s, cur, writers, cs) {
                    return None;
                }
                let mut all = Carry::Unknown;
                for b in bs {
                    if self.writes(&b.guard, cur, writers, cs) {
                        return None;
                    }
                    all = merge(all, self.carry(&b.body, cur, writers, carriers)?);
                }
                Some(all)
            }
            E::Record(_, fs, _, _) => {
                let mut found = None;
                for f in fs {
                    if self.is_alias(&f.value, cur, cs) {
                        found = Some(match found {
                            None => Carry::Field(self.text(f.name).to_string()),
                            Some(_) => Carry::Opaque,
                        });
                    } else if self.carry(&f.value, cur, writers, carriers).is_some() {
                        found = Some(Carry::Opaque);
                    }
                }
                found
            }
            _ if self.is_alias(e, cur, cs) => Some(Carry::Whole),
            E::Apply(..) => {
                let (head, args) = call_spine(e);
                let E::Name(n, _, _) = head else { return None };
                if self.text(*n).starts_with(|c: char| c.is_ascii_uppercase()) {
                    args.iter().any(|a| self.carry(a, cur, writers, carriers).is_some()).then_some(Carry::Opaque)
                } else {
                    self.carried_arg(*n, &args, cur, carriers)
                }
            }
            _ => None,
        }
    }

    /// How a call expression hands back the list `cur` holds.
    fn carried_call(&self, e: &IrExpr, cur: &[Holder], carriers: &Carriers) -> Option<Carry> {
        let (head, args) = call_spine(e);
        let IrExpr::Name(n, _, _) = head else { return None };
        self.carried_arg(*n, &args, cur, carriers)
    }

    /// Whether a body binds the answer of a `list-set-at` to a name nothing
    /// reads, or runs one as a statement and discards its answer.
    fn drops_a_write(&self, body: &IrExpr) -> bool {
        let mut hit = false;
        body.walk(&mut |x| match x {
            IrExpr::Let(n, _, v, b, _) if self.is_set_at(v) && !mentions(b, *n) => hit = true,
            IrExpr::Act(stmts, _, _) => {
                if stmts.iter().any(|s| matches!(s, IrActStmt::Exec(e, _) if self.is_set_at(e))) {
                    hit = true;
                }
            }
            _ => {}
        });
        hit
    }

    fn is_set_at(&self, e: &IrExpr) -> bool {
        let (head, args) = call_spine(e);
        args.len() == 3 && matches!(head, IrExpr::Name(n, _, _) if self.text(*n) == "list-set-at")
    }
}

/// A call's head and its arguments in order.
fn call_spine(e: &IrExpr) -> (&IrExpr, Vec<&IrExpr>) {
    let mut head = e;
    let mut args = Vec::new();
    while let IrExpr::Apply(f, a, _, _) = head {
        args.push(&**a);
        head = f;
    }
    args.reverse();
    (head, args)
}

/// A field access's slot is spelled `name/slot`.
fn field_name(slot: &str) -> &str {
    slot.split('/').next().unwrap_or(slot)
}

fn mentions(e: &IrExpr, n: Sym) -> bool {
    let mut hit = false;
    e.walk(&mut |x| {
        if matches!(x, IrExpr::Name(m, _, _) if *m == n) {
            hit = true;
        }
    });
    hit
}
