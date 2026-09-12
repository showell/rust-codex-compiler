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
const KEYWORDS: [&str; 25] = [
    "and", "app", "as", "crash", "dbg", "else", "expect", "exposes", "exposing", "for", "if", "import", "in",
    "match", "module", "or", "packages", "platform", "provides", "requires", "return", "targets", "var", "where",
    "while",
];

/// Roc's own type names: a chapter that declares one of these spells it
/// with a trailing underscore, since a declared `Box` reads as the
/// builtin's and Roc asks it for a type argument (codex/test's
/// literal-subpattern, tco-direct-arg-reads).
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

/// **CODEX WRITES A LIST IN PLACE; ROC ANSWERS A NEW ONE.** The two agree
/// wherever the program uses the answer, and diverge wherever it uses the
/// list it wrote through another name. Two shapes say the write was for
/// its effect, and both are refused rather than emitted wrongly:
///
/// - a definition that writes one of its own list parameters and answers
///   something that is not a list (the foreword's `cb-shl1-step` doubles a
///   bignum in place and answers the carry, and its caller reads the
///   doubled list);
/// - a `let` whose value is such a write and whose name nothing reads.
///
/// The verdicts that pin the behaviour are `codex/test/edalias` and
/// `cryptobig`, and both were answering quietly wrong numbers before this.
/// A definition's result: `k` parameters peel `k` arrows.
fn result_ty(t: &Ty, k: usize) -> Ty {
    let mut cur = t.clone();
    for _ in 0..k {
        loop {
            match cur {
                Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => cur = *b,
                _ => break,
            }
        }
        match cur {
            Ty::Fun(_, _, r) => cur = *r,
            other => return other,
        }
    }
    cur
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
const PRELUDE: &str = r#"# Prelude -- what no chapter declares, written by rocemit. Do not edit.

Prelude :: [].{
	Maybe(a) : [None, Just(a)]

	int_mod : I64, I64 -> I64
	int_mod = |a, b| {
		m = I64.mod_by(a, b)
		if m < 0 { m + I64.abs(b) } else { m }
	}
}
"#;

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
pub fn emit_modules(
    ch: &Chapter,
    tds: &TypeDefs,
    syms: &SymTab,
    defs: &[IrDef],
) -> Result<Vec<(String, String)>, String> {
    let mut cx = Cx::new(ch, tds, syms, defs);
    // **A UNIT WITH NO OPENING IS A LIBRARY**: every chapter a module, no
    // app. That is what a GPU kernel chapter is.
    // A `[Device]` opening (GlobeKernels has one, for the wgsl plug's root)
    // is a kernel like any other, not a main.
    let device_defs = cx.device_defs.clone();
    let is_main = |d: &IrDef| syms.text(d.name) == "opening" && !device_defs.contains(&d.name);
    let app_slug = defs.iter().find(|d| is_main(d)).map(|a| a.origin.clone()).unwrap_or_default();
    cx.app = app_slug.clone();
    let mut slugs: Vec<String> = Vec::new();
    for d in defs {
        if d.origin.is_empty() {
            return Err(format!("`{}` belongs to no chapter", syms.text(d.name)));
        }
        if !slugs.contains(&d.origin) {
            slugs.push(d.origin.clone());
        }
    }
    for c in &ch.type_def_chapters {
        if !slugs.contains(c) {
            slugs.push(c.clone());
        }
    }
    let mut files = Vec::new();
    let mut prelude = false;
    for slug in &slugs {
        module_name(slug)?;
        cx.current = slug.clone();
        cx.imports.clear();
        let mut items = String::new();
        let base = if *slug == app_slug { 0 } else { 1 };
        for (td, c) in ch.type_defs.iter().zip(&ch.type_def_chapters) {
            if c == slug {
                items.push_str(&cx.type_def(td, base)?);
            }
        }
        let mut main = None;
        for d in defs.iter().filter(|d| d.origin == *slug) {
            if is_main(d) {
                main = Some(cx.opening(d)?);
                continue;
            }
            items.push('\n');
            items.push_str(&cx.def(d, base)?);
        }
        if items.is_empty() && main.is_none() {
            continue;
        }
        prelude |= cx.imports.contains("Prelude");
        let mut text = format!("# {slug} -- emitted from Codex by rocemit (rust-codex-compiler). Do not edit.\n");
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
            text.push_str(&format!("\n{slug} :: [].{{\n{items}}}\n"));
        }
        files.push((format!("{slug}.roc"), text));
    }
    if cx.uses_cce {
        files.push(("Cce.roc".into(), cce_module()));
    }
    if prelude {
        files.push((
            "Prelude.roc".into(),
            PRELUDE.into(),
        ));
    }
    Ok(files)
}

/// A chapter slug as a Roc module name: capitalised, alphanumeric.
fn module_name(slug: &str) -> Result<&str, String> {
    if slug.starts_with(|c: char| c.is_ascii_uppercase()) && slug.chars().all(|c| c.is_ascii_alphanumeric()) {
        Ok(slug)
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
    /// The chapter's derived `__eq_<T>`, by the type it compares. A nominal
    /// type has no structural `==`, so the one Codex derived is attached to
    /// it as the `is_eq` method Roc's `==` dispatches to.
    derived_eq: BTreeMap<Sym, Sym>,
    imports: std::collections::BTreeSet<String>,
    /// Names bound by the enclosing parameters, lets and patterns.
    locals: Vec<Sym>,
    /// Type-variable letters, per definition signature.
    tvars: BTreeMap<u32, String>,
    uses_line: bool,
    /// Set when the unit reaches for the alphabet, which is then emitted
    /// beside the chapters as `Cce.roc`.
    uses_cce: bool,
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
    /// The name holding the device at this point of an effectful body, and
    /// the count of names minted for it in this definition.
    dev: Option<String>,
    dev_n: usize,
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

struct Fold {
    name: Sym,
    helper: String,
    acc: String,
}

impl<'a> Cx<'a> {
    fn new(ch: &Chapter, tds: &'a TypeDefs, syms: &'a SymTab, defs: &'a [IrDef]) -> Cx<'a> {
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
            derived_eq: BTreeMap::new(),
            imports: Default::default(),
            locals: Vec::new(),
            tvars: BTreeMap::new(),
            uses_line: false,
            uses_cce: false,
            fold: None,
            device_ops: Default::default(),
            device_defs: Default::default(),
            dev: None,
            dev_n: 0,
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
        for (td, c) in ch.type_defs.iter().zip(&ch.type_def_chapters) {
            let n = match td {
                TypeDef::Record(n, ..) | TypeDef::Variant(n, ..) | TypeDef::Unit(n, ..) => *n,
            };
            cx.type_module.insert(n, c.clone());
        }
        for d in defs {
            cx.def_module.insert(d.name, d.origin.clone());
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
        for d in defs {
            if let Some(t) = syms.text(d.name).strip_prefix("__eq_") {
                if let Some(n) = syms.find(t).filter(|n| cx.type_module.contains_key(n)) {
                    cx.derived_eq.insert(n, d.name);
                }
            }
        }
        cx
    }

    /// A name from module `module`, as seen from the module being emitted:
    /// bare at home, `Module.name` elsewhere, and the import is remembered.
    fn qualified(&mut self, module: &str, name: String) -> String {
        if module.is_empty() || module == self.current {
            return name;
        }
        self.imports.insert(module.to_string());
        format!("{module}.{name}")
    }

    /// A definition's name as a reference.
    fn def_ref(&mut self, n: Sym) -> Result<String, String> {
        let m = self.def_module.get(&n).cloned().unwrap_or_default();
        let id = self.ident(n)?;
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
            self.imports.insert(m.clone());
        }
        format!("{m}.{name}")
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
        Ok(if collides { format!("{id}_") } else { id })
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
            // A Codex Char is its code in the alphabet (see `cce_module`).
            Ty::Char => "I64".into(),
            Ty::Real(RealWidth::F64, _) => self.real().into(),
            Ty::Text => "Str".into(),
            Ty::Boolean => "Bool".into(),
            Ty::Nothing => "{}".into(),
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
    /// last.
    fn device_signature(&mut self, d: &IrDef) -> Result<String, String> {
        let (ps, r, _) = self.arrows(d)?;
        let mut all = vec!["Device.Device".to_string()];
        all.extend(ps);
        let sig = format!("{} -> (Device.Device, {r})", all.join(", "));
        let wants = self.eq_wants(d)?;
        Ok(if wants.is_empty() { sig } else { format!("{sig} where [{}]", wants.join(", ")) })
    }

    /// `k` parameters peel `k` arrows: the parameter types, the result, and
    /// whether any of those arrows performs an effect.
    fn arrows(&mut self, d: &IrDef) -> Result<(Vec<String>, String, bool), String> {
        self.tvars.clear();
        let mut cur = &d.ty;
        let mut ps = Vec::new();
        let mut eff = false;
        for _ in 0..d.params.len() {
            loop {
                match cur {
                    Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => cur = b,
                    _ => break,
                }
            }
            match cur {
                Ty::Fun(p, row, r) => {
                    eff |= !row.labels.is_empty();
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
        // A nullary `[Device] T` is effectful in its type; the device
        // signature carries the effect, so the result is the T.
        let r = match cur {
            Ty::Effectful(_, _, inner) if self.has_device(cur) => self.ty(inner)?,
            _ => self.ty(cur)?,
        };
        Ok((ps, r, eff))
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
                "Char" => "I64".into(),
                "Text" => "Str".into(),
                "Boolean" => "Bool".into(),
                "Nothing" => "{}".into(),
                s if s.starts_with(|c: char| c.is_ascii_lowercase()) => s.to_string(),
                _ => self.type_ref(*n),
            },
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

    /// **A NOMINAL TYPE HAS NO STRUCTURAL `==`.** An alias is compared
    /// field by field; a `:=` type is asked for its `is_eq` method, and a
    /// list or record holding one is compared through that. Codex derives
    /// the equality already, so the nominal declaration carries it as a
    /// forwarder and `==` works on the type wherever it appears
    /// (codex/test's shell-build-keep).
    fn methods(&mut self, n: Sym, base: usize) -> Result<String, String> {
        if !self.recursive.contains(&n) {
            return Ok(String::new());
        }
        let Some(eq) = self.derived_eq.get(&n).copied() else {
            return Ok(String::new());
        };
        let Some(d) = self.defs.iter().find(|d| d.name == eq) else {
            return Ok(String::new());
        };
        let sig = self.signature(d)?;
        let call = self.def_ref(eq)?;
        let t = "\t".repeat(base + 1);
        Ok(format!(".{{\n{t}is_eq : {sig}\n{t}is_eq = |a, b| {call}(a, b)\n{}}}", "\t".repeat(base)))
    }

    /// The name of a list parameter this body writes with `list-set-at`.
    fn written_param(&self, body: &IrExpr, params: &[Sym]) -> Option<String> {
        let mut found = None;
        body.walk(&mut |x| {
            let mut head = x;
            let mut args: Vec<&IrExpr> = Vec::new();
            while let IrExpr::Apply(f, a, _, _) = head {
                args.push(a);
                head = f;
            }
            args.reverse();
            if let IrExpr::Name(n, _, _) = head {
                if args.len() == 3 && self.syms.text(*n) == "list-set-at" {
                    if let IrExpr::Name(t, _, _) = args[0] {
                        if params.contains(t) && found.is_none() {
                            found = Some(self.syms.text(*t).to_string());
                        }
                    }
                }
            }
        });
        found
    }

    /// `:` for a plain alias, `:=` for one that stands on a cycle.
    fn colon(&self, n: Sym) -> &'static str {
        if self.recursive.contains(&n) { ":=" } else { ":" }
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
                    fs.push(format!("{} : {}", self.ident(f.name)?, self.texpr(&f.type_expr)?));
                }
                let col = self.colon(*n);
                let body = if fs.is_empty() { "{}".to_string() } else { format!("{{ {} }}", fs.join(", ")) };
                format!("{tabs}{} {col} {body}{}\n", head(*n, ps)?, self.methods(*n, base)?)
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
                    self.methods(*n, base)?
                )
            }
            TypeDef::Unit(n, ..) => return Err(format!("unit type `{}`", self.syms.text(*n))),
        })
    }

    // ---- definitions ----------------------------------------------------

    /// A definition, or the line that says a data table was left to a baker.
    ///
    /// **A DATA TABLE IS NOT EMITTED, AND THE OMISSION IS WRITTEN DOWN.**
    /// A definition, whole; a data table of thousands of literals is emitted
    /// as the literal it is, since the nightly's checker is linear in them.
    fn def(&mut self, d: &IrDef, base: usize) -> Result<String, String> {
        let name = self.ident(d.name)?;
        // A write to a list parameter, in a definition that answers
        // something else, is a mutation the caller reads back (see
        // `writes_a_param`).
        let ps: Vec<Sym> = d.params.iter().map(|p| p.name).collect();
        let (_, ret, _) = self.arrows(d)?;
        if !matches!(result_ty(&d.ty, d.params.len()), Ty::List(_)) {
            let _ = &ret;
            if let Some(t) = self.written_param(&d.body, &ps) {
                return Err(format!("`{}` writes its list parameter `{t}` and answers something else", self.syms.text(d.name)));
            }
        }
        let sig = self.signature(d)?;
        let mark = self.locals.len();
        let mut ps = Vec::new();
        for p in &d.params {
            self.locals.push(p.name);
            ps.push(self.binder(p.name, &[&d.body])?);
        }
        let tabs = "\t".repeat(base);
        if self.device_defs.contains(&d.name) {
            self.imports.insert("Device".into());
            for p in &d.params {
                self.no_dev_name(p.name)?;
            }
            self.dev_n = 0;
            self.dev = Some("dev".into());
            let sig = self.device_signature(d)?;
            let body = self.eff_expr(&d.body, base)?;
            self.dev = None;
            self.locals.truncate(mark);
            let mut all = vec!["dev".to_string()];
            all.extend(ps);
            return Ok(format!("{tabs}{name} : {sig}\n{tabs}{name} = |{}| {body}\n", all.join(", ")));
        }
        // **A RIGHT FOLD IS EMITTED AS AN ACCUMULATOR LOOP.** Codex builds a
        // list by `x & f rest`: the recursive call is the right operand of
        // an append, and each level copies everything below it, so a
        // 2,430-element list costs 1.7 seconds in Roc where an accumulator
        // costs milliseconds (measured, roc-apps probe/cons). The shape is
        // recognised, not guessed: every recursive call sits as the right
        // operand of an append at a leaf of the if-tree, and nowhere else.
        let out = if !ps.is_empty() && is_right_fold(&d.body, d.name) {
            let acc = self.syms.find("acc").filter(|a| self.locals.contains(a)).map_or("acc", |_| "acc_");
            let helper = format!("{name}_acc");
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
            self.fold = Some(Fold { name: d.name, helper: helper.clone(), acc: acc.to_string() });
            let body = self.expr(&d.body, base)?;
            self.fold = None;
            format!(
                "{tabs}# {name} builds its list by appending a recursive call; emitted as an accumulator loop, which is linear where the direct shape is quadratic.\n\
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

    /// `opening : [Console] Nothing = act ...` is `main!`.
    fn opening(&mut self, d: &IrDef) -> Result<String, String> {
        if !d.params.is_empty() {
            return Err("opening takes parameters".into());
        }
        let mark = self.locals.len();
        let mut out = String::from("main! = |_args| {\n");
        // **AN OPENING MAY BE WRAPPED IN LETS**, and upstream runs the act
        // inside them; the bindings are main!'s own.
        let mut body = &d.body;
        while let IrExpr::Let(n, _, v, inner, _) = body {
            let v = self.expr(v, 1)?;
            self.locals.push(*n);
            out.push_str(&format!("\t{} = {v}\n", self.local(*n)?));
            body = inner;
        }
        // **AN OPENING THAT IS A VALUE IS PRINTED**, which is what the
        // driver does with it and what every verdict in codex/test records.
        let IrExpr::Act(stmts, _, _) = body else {
            let text = match body.ty() {
                Ty::Text => self.expr(body, 1)?,
                Ty::Integer(..) => format!("I64.to_str({})", self.expr(body, 1)?),
                other => {
                    return Err(format!(
                        "an opening of type {}",
                        crate::ir_text::render_ty(self.syms, &other)
                    ))
                }
            };
            self.uses_line = true;
            out.push_str(&format!("\tline!({text})\n\tOk({{}})\n}}\n"));
            self.locals.truncate(mark);
            return Ok(out);
        };
        for s in stmts {
            match s {
                IrActStmt::Exec(e, _) => {
                    let e = self.expr(e, 1)?;
                    out.push_str(&format!("\t{e}\n"));
                }
                IrActStmt::Bind(n, _, e, _) => {
                    let e = self.expr(e, 1)?;
                    self.locals.push(*n);
                    out.push_str(&format!("\t{} = {e}\n", self.local(*n)?));
                }
            }
        }
        self.locals.truncate(mark);
        out.push_str("\tOk({})\n}\n");
        Ok(out)
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
            E::Name(n, _, _) => self.is_device_sym(*n),
            E::Apply(..) => {
                let mut head = e;
                while let E::Apply(f, _, _, _) = head {
                    head = f;
                }
                matches!(head, E::Name(n, _, _) if self.is_device_sym(*n))
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

    /// The threaded device is `dev`, `dev1`, `dev2`, ...: a Codex name
    /// spelled like one would shadow it.
    fn no_dev_name(&self, n: Sym) -> Result<(), String> {
        let id = self.ident(n)?;
        if id.starts_with("dev") && id[3..].chars().all(|c| c.is_ascii_digit()) {
            return Err(format!("`{id}` is spelled like the threaded device"));
        }
        Ok(())
    }

    fn fresh_dev(&mut self) -> String {
        self.dev_n += 1;
        format!("dev{}", self.dev_n)
    }

    fn cur_dev(&self) -> Result<String, String> {
        self.dev.clone().ok_or_else(|| "the Device effect outside a [Device] definition".to_string())
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
            return Ok(format!("({dev}, {})", self.expr(e, ind)?));
        }
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
                                out.push_str(&format!("{tabs}_ = {}\n", self.expr(x, ind + 1)?));
                            }
                        }
                        IrActStmt::Bind(n, _, x, _) => {
                            self.no_dev_name(*n)?;
                            if self.is_effectful(x) {
                                let v = self.eff_expr(x, ind + 1)?;
                                let d = self.fresh_dev();
                                self.locals.push(*n);
                                let b = if i == last { self.local(*n)? } else { self.binder(*n, &rest)? };
                                out.push_str(&format!("{tabs}({d}, {b}) = {v}\n"));
                                self.dev = Some(d);
                            } else {
                                let v = self.expr(x, ind + 1)?;
                                self.locals.push(*n);
                                let b = if i == last { self.local(*n)? } else { self.binder(*n, &rest)? };
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
            E::Let(..) => {
                let tabs = "\t".repeat(ind + 1);
                let mut out = String::from("({\n");
                let mark = self.locals.len();
                let mut cur = e;
                while let E::Let(n, _, v, body, _) = cur {
                    if self.is_effectful(v) {
                        return Err("an effectful let".into());
                    }
                    self.no_dev_name(*n)?;
                    let v = self.expr(v, ind + 1)?;
                    self.locals.push(*n);
                    let b = self.binder(*n, &[body])?;
                    out.push_str(&format!("{tabs}{b} = {v}\n"));
                    cur = body;
                }
                out.push_str(&format!("{tabs}{}\n{}}})", self.eff_expr(cur, ind + 1)?, "\t".repeat(ind)));
                self.locals.truncate(mark);
                out
            }
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
            E::Match(..) => return Err("a match under the Device effect".into()),
            _ => return Err("an effectful form".into()),
        };
        self.dev = Some(dev);
        Ok(out)
    }

    /// A call under the Device effect: a `[Device]` definition with the
    /// device first, or one of the effect's operations on the Device module.
    fn eff_call(&mut self, n: Sym, args: &[&IrExpr], ind: usize) -> Result<String, String> {
        let mut xs = vec![self.cur_dev()?];
        for a in args {
            if self.is_effectful(a) {
                return Err("an effectful argument".into());
            }
            xs.push(self.expr(a, ind)?);
        }
        let text = self.syms.text(n).to_string();
        if self.device_defs.contains(&n) {
            let k = self.arity[&n];
            if args.len() != k {
                return Err(format!("`{text}` applied to {} of {k} arguments under Device", args.len()));
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
        self.imports.insert("Device".into());
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
    fn binder(&self, n: Sym, scope: &[&IrExpr]) -> Result<String, String> {
        let used = scope.iter().any(|e| uses(e, n));
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
            E::TextLit(s, _) => roc_quote(s),
            E::BoolLit(b, _) => if *b { "True".into() } else { "False".into() },
            // The IR carries a char literal as its CODE already.
            E::CharLit(c, _) => int_lit(*c),
            E::Name(n, _, _) => self.name_value(*n)?,
            E::Binary(op, l, r, t, _) => {
                let (l, r) = (self.expr(l, ind)?, self.expr(r, ind)?);
                // **THE OVERFLOW MODE IS ON THE TYPE.** A field declared
                // `Integer between lo and hi wrapping` (Rng's LCG state) wraps
                // where Roc's `+` would crash; the checker carries the mode on
                // every node of that type, so the spelling follows the node.
                let wrap = matches!(t, Ty::Integer(_, _, crate::check::Overflow::Wrapping));
                if matches!(t, Ty::Integer(_, _, crate::check::Overflow::Clamping)) {
                    return Err("a clamping integer".into());
                }
                self.binary(*op, l, r, wrap)?
            }
            E::Negate(x, t, _) => {
                let x = self.expr(x, ind)?;
                if self.wgsl && matches!(t, Ty::Integer(..)) {
                    format!("{}.minus_wrap(0, {x})", self.int())
                } else {
                    format!("(-{x})")
                }
            }
            E::If(c, t, f, _, _) => format!(
                "(if {} {{ {} }} else {{ {} }})",
                self.expr(c, ind)?,
                self.expr(t, ind)?,
                self.expr(f, ind)?
            ),
            E::Let(..) => self.let_block(e, ind)?,
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
                let mut out = format!("(match {} {{\n", self.expr(sc, ind)?);
                for b in bs {
                    let mark = self.locals.len();
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
            E::Act(..) => return Err("an act outside opening".into()),
            E::Record(_, fs, _, _) => {
                if fs.is_empty() {
                    return Ok("{}".into());
                }
                let mut items = Vec::new();
                for f in fs {
                    items.push(format!("{}: {}", self.ident(f.name)?, self.expr(&f.value, ind)?));
                }
                format!("{{ {} }}", items.join(", "))
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
            return Err(format!("`{}` performs the Device effect outside a statement", self.syms.text(n)));
        }
        if self.arity.contains_key(&n) {
            return self.def_ref(n);
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

    /// A `let` chain is one block: `({ a = .. \n b = .. \n body })`. The parens
    /// keep it an expression -- a bare `{` opens a record.
    fn let_block(&mut self, e: &IrExpr, ind: usize) -> Result<String, String> {
        let tabs = "\t".repeat(ind + 1);
        let mut out = String::from("({\n");
        let mark = self.locals.len();
        let mut cur = e;
        while let IrExpr::Let(n, _, v, body, _) = cur {
            let v = self.expr(v, ind + 1)?;
            self.locals.push(*n);
            let b = self.binder(*n, &[body])?;
            out.push_str(&format!("{tabs}{b} = {v}\n"));
            cur = body;
        }
        out.push_str(&format!("{tabs}{}\n{}}})", self.expr(cur, ind + 1)?, "\t".repeat(ind)));
        self.locals.truncate(mark);
        Ok(out)
    }

    fn binary(&mut self, op: IrBinOp, l: String, r: String, wrap: bool) -> Result<String, String> {
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
        Ok(match op {
            B::AddInt | B::AddNum => format!("({l} + {r})"),
            B::SubInt | B::SubNum => format!("({l} - {r})"),
            B::MulInt | B::MulNum => format!("({l} * {r})"),
            B::DivNum => format!("({l} / {r})"),
            B::DivInt => format!("{int}.div_trunc_by({l}, {r})"),
            B::RemInt => format!("{int}.rem_by({l}, {r})"),
            B::PowInt => format!("{int}.pow({l}, {r})"),
            B::Eq => format!("({l} == {r})"),
            B::NotEq => format!("({l} != {r})"),
            B::Lt => format!("({l} < {r})"),
            B::Gt => format!("({l} > {r})"),
            B::LtEq => format!("({l} <= {r})"),
            B::GtEq => format!("({l} >= {r})"),
            B::And => format!("({l} and {r})"),
            B::Or => format!("({l} or {r})"),
            B::AppendText => format!("Str.concat({l}, {r})"),
            B::AppendList => format!("List.concat({l}, {r})"),
            // `=~=` is ordinal equality on doubles; two doubles with the same
            // bits have the same ordinal, and -0.0 differs from 0.0 in both.
            B::ApproxEqExact => format!("({real}.to_bits({l}) == {real}.to_bits({r}))", real = self.real()),
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
        let IrExpr::Name(n, _, _) = head else {
            return Err("a call whose head is not a name".into());
        };
        let n = &self.instance_base(*n);
        let text = self.syms.text(*n).to_string();
        if self.is_device_sym(*n) {
            return Err(format!("`{text}` performs the Device effect outside a statement"));
        }
        let mut xs = Vec::new();
        for a in &args {
            xs.push(self.expr(a, ind)?);
        }
        if self.locals.contains(n) {
            return Ok(format!("{}({})", self.local(*n)?, xs.join(", ")));
        }
        if let Some(&k) = self.arity.get(n) {
            if xs.len() < k {
                return Err(format!("`{text}` applied to {} of {k} arguments", xs.len()));
            }
            let first = format!("{}({})", self.def_ref(*n)?, xs[..k].join(", "));
            return Ok(if xs.len() == k { first } else { format!("{first}({})", xs[k..].join(", ")) });
        }
        if text.starts_with(|c: char| c.is_ascii_uppercase()) {
            return Ok(format!("{}({})", self.tag(*n)?, xs.join(", ")));
        }
        self.builtin(&text, &args, xs)
    }

    fn builtin(&mut self, name: &str, args: &[&IrExpr], xs: Vec<String>) -> Result<String, String> {
        let want = |k: usize| -> Result<(), String> {
            if xs.len() == k {
                Ok(())
            } else {
                Err(format!("`{name}` applied to {} arguments, takes {k}", xs.len()))
            }
        };
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
            // **CODEX MUTATES IN PLACE; ROC ANSWERS A NEW LIST.** The two
            // agree when the program uses the answer, which is what every
            // typed use does; a program that relies on the aliasing (sets and
            // then reads the old name) diverges silently, and only a verdict
            // catches it. Past the end is a crash in both.
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
            "char-code" | "code-to-char" => {
                want(1)?;
                // A Char IS its code here, so both are the value.
                xs[0].clone()
            }
            "char-code-at" => {
                want(2)?;
                self.uses_cce = true;
                self.imports.insert("Cce".into());
                format!("Cce.at({}, {})", xs[0], xs[1])
            }
            "char-at" => {
                want(2)?;
                self.uses_cce = true;
                self.imports.insert("Cce".into());
                format!("Cce.at_or_crash({}, {})", xs[0], xs[1])
            }
            "char-to-text" | "char-encode" => {
                want(1)?;
                self.uses_cce = true;
                self.imports.insert("Cce".into());
                format!("Cce.text({})", xs[0])
            }
            // The classifiers are code RANGES, not the host's idea of a
            // letter: the alphabet is frequency-ordered (interp.rs).
            "is-letter" => {
                want(1)?;
                format!("(({x} >= 13 and {x} <= 64) or ({x} >= 97 and {x} <= 127))", x = xs[0])
            }
            "is-digit" => {
                want(1)?;
                format!("({x} >= 3 and {x} <= 12)", x = xs[0])
            }
            "is-whitespace" => {
                want(1)?;
                format!("({x} >= 1 and {x} <= 2)", x = xs[0])
            }
            "substring" => {
                want(3)?;
                self.uses_cce = true;
                self.imports.insert("Cce".into());
                format!("Cce.substring({}, {}, {})", xs[0], xs[1], xs[2])
            }
            // `__narrow` is the checker's marker for a value proved to fit a
            // bound; at runtime it is the value (interp.rs).
            "__narrow" => {
                want(1)?;
                xs[0].clone()
            }
            "list-push" | "list-snoc" => {
                want(2)?;
                format!("List.append({}, {})", xs[0], xs[1])
            }
            // `show` is Codex's own spelling of a value, not Roc's: a
            // boolean is `True` or `False` (interp::show).
            "show" | "integer-to-text" => {
                want(1)?;
                match args[0].ty() {
                    Ty::Integer(..) => format!("{int}.to_str({})", xs[0]),
                    Ty::Boolean => format!("(if {} {{ \"True\" }} else {{ \"False\" }})", xs[0]),
                    Ty::Text => xs[0].clone(),
                    Ty::Char => {
                        self.uses_cce = true;
                self.imports.insert("Cce".into());
                        format!("Cce.text({})", xs[0])
                    }
                    other => return Err(format!("show on a {}", crate::ir_text::render_ty(self.syms, &other))),
                }
            }
            // A Codex Text is CCE units over an alphabet of 1..127, so its
            // length is its byte count.
            "text-length" => {
                want(1)?;
                self.uses_cce = true;
                self.imports.insert("Cce".into());
                format!("Cce.length({})", xs[0])
            }
            // `text-to-integer` trims and answers 0 for anything it cannot
            // read, as the interpreter does.
            "text-to-integer" => {
                want(1)?;
                format!("({int}.from_str(Str.trim({})) ?? 0)", xs[0])
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
            // Roc's I64 has no shift; a shift by b is a wrapping multiply or
            // an unsigned divide by 2^b, which is what the interpreter does.
            "bit-shl" => {
                want(2)?;
                format!(
                    "U64.to_i64_wrap(U64.times_wrap(I64.to_u64_wrap({}), U64.pow(2, I64.to_u64_wrap({}))))",
                    xs[0], xs[1]
                )
            }
            "bit-shr" | "bit-shru" => {
                want(2)?;
                format!(
                    "U64.to_i64_wrap(U64.div_by(I64.to_u64_wrap({}), U64.pow(2, I64.to_u64_wrap({}))))",
                    xs[0], xs[1]
                )
            }
            "print-line-uni" => {
                want(1)?;
                self.uses_line = true;
                format!("line!({})", xs[0])
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
            IrPat::Lit(v, ty, _) => match ty {
                Ty::Integer(..) | Ty::Char => v.clone(),
                Ty::Text => roc_quote(v),
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
                self.fold = Some(Fold { name: fold.name, helper: fold.helper.clone(), acc: fold.acc.clone() });
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
                while let E::Let(n, _, v, body, _) = cur {
                    let v = self.expr(v, ind + 1)?;
                    self.locals.push(*n);
                    let b = self.binder(*n, &[body])?;
                    out.push_str(&format!("{tabs}{b} = {v}\n"));
                    cur = body;
                }
                self.fold = Some(Fold { name: fold.name, helper: fold.helper.clone(), acc: fold.acc.clone() });
                let last = self.expr(cur, ind + 1);
                self.fold = None;
                out.push_str(&format!("{tabs}{}\n{}}})", last?, "\t".repeat(ind)));
                self.locals.truncate(mark);
                Ok(out)
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

/// A Codex name as a Roc identifier: kebab to snake, keywords suffixed. A
/// lifted `__lam_0` loses its underscores, which in Roc would mark it unused,
/// and a derived `__eq_Tup2` loses its capitals, which Roc reads as a type.
fn ident_text(t: &str) -> Result<String, String> {
    let t = t.trim_start_matches('_');
    if t.is_empty() {
        return Err("a name of only underscores cannot be a Roc identifier".into());
    }
    if !t.chars().all(|c| c.is_ascii_alphanumeric() || c == '-' || c == '_') {
        return Err(format!("name `{t}` cannot be a Roc identifier"));
    }
    let s = t.replace('-', "_").to_ascii_lowercase();
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

fn roc_quote(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\t' => out.push_str("\\t"),
            '$' => out.push_str("\\$"),
            other => out.push(other),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod literals_round_trip {
    use super::num_lit;

    #[test]
    fn the_fourth_case_keeps_its_digits() {
        let bits = 0.012500000000000011_f64.to_bits() as i64;
        assert_eq!(num_lit(bits), "0.012500000000000011");
    }

    #[test]
    fn a_negative_is_parenthesised() {
        assert_eq!(num_lit((-0.25_f64).to_bits() as i64), "(-0.25)");
    }

    #[test]
    fn an_exponent_goes_through_bits() {
        assert_eq!(num_lit(1e21_f64.to_bits() as i64), format!("F64.from_bits({})", 1e21_f64.to_bits()));
    }
}

/// **THE CODEX ALPHABET, WRITTEN OUT FOR ROC.** A Codex `Char` is not a
/// byte and not a Unicode scalar: it is a code in a private,
/// frequency-ordered alphabet of 1..127, where `char-code 'A'` is 41 and
/// the codes above 96 are accented Latin and Cyrillic. A Codex `Text` is a
/// sequence of those units, one per CHARACTER, so its length and its
/// indexing are by character and not by byte.
///
/// So a Char emits as its code, an `I64`, and this module is what turns a
/// Roc `Str` into codes and back. It is GENERATED from `charcode.rs`'s own
/// tables rather than transcribed, because that file says in as many words
/// that the tables cannot be transcribed by hand: ten corpus programs once
/// differed from the oracle by exactly 61 bytes, a run of NULs where the
/// Cyrillic should have been.
fn cce_module() -> String {
    let mut points = [0u32; 128];
    for (b, code) in crate::charcode::CHAR_CODE.iter().enumerate() {
        if *code != 0 {
            points[*code as usize] = b as u32;
        }
    }
    for (i, c) in crate::charcode::CHAR_CODE_HIGH.iter().enumerate() {
        points[crate::charcode::HIGH_BASE as usize + i] = *c as u32;
    }
    let codes: Vec<String> = crate::charcode::CHAR_CODE.iter().map(|c| c.to_string()).collect();
    let pts: Vec<String> = points.iter().map(|p| p.to_string()).collect();
    let wrap = |xs: &[String]| -> String {
        xs.chunks(16).map(|c| format!("\t\t{}", c.join(", "))).collect::<Vec<_>>().join(",\n")
    };
    format!(
        r#"# Cce -- the Codex character alphabet, written from the compiler's own
# tables by rocemit (rust-codex-compiler). Do not edit.
#
# A Codex Char is its CODE in a private frequency-ordered alphabet of
# 1..127: `char-code 'A'` is 41, not 65. Codes 97..127 are accented Latin
# and Cyrillic, which no byte reaches. A Codex Text is a sequence of those
# units, ONE PER CHARACTER, so `text-length` counts characters and
# `char-code-at` indexes them.

Cce :: [].{{
	# The code of each of the first 128 Unicode code points; 0 for a point
	# the alphabet does not name.
	codes : List(I64)
	codes = [
{codes}
	]

	# The code point each code names, indexed by code; 0 for none.
	points : List(U64)
	points = [
{points}
	]

	# The code of one Unicode code point, or 0.
	of_point : U64 -> I64
	of_point = |p|
		if p < 128 {{ List.get(Cce.codes, p) ?? 0 }} else {{ Cce.high_of(p, 97) }}

	high_of : U64, I64 -> I64
	high_of = |p, c|
		if c > 127 {{ 0 }}
		else if (List.get(Cce.points, I64.to_u64_wrap(c)) ?? 0) == p {{ c }}
		else {{ Cce.high_of(p, c + 1) }}

	# A text as its codes, one per character.
	codes_of : Str -> List(I64)
	codes_of = |s| Cce.decode(Str.to_utf8(s), 0, [])

	decode : List(U8), U64, List(I64) -> List(I64)
	decode = |bytes, i, acc|
		if i >= List.len(bytes) {{ acc }} else {{
			b = U8.to_u64(List.get(bytes, i) ?? 0)
			# The alphabet reaches no further than two UTF-8 bytes, but a
			# text may hold anything; a character the alphabet does not
			# name is code 0, as `char-code` answers.
			width = if b < 128 {{ 1 }} else if b < 224 {{ 2 }} else if b < 240 {{ 3 }} else {{ 4 }}
			point = if width == 1 {{ b }} else {{
				Cce.tail(bytes, i + 1, i + width, Cce.lead(b, width))
			}}
			Cce.decode(bytes, i + width, List.append(acc, Cce.of_point(point)))
		}}

	lead : U64, U64 -> U64
	lead = |b, width|
		if width == 2 {{ U64.bitwise_and(b, 31) }}
		else if width == 3 {{ U64.bitwise_and(b, 15) }}
		else {{ U64.bitwise_and(b, 7) }}

	tail : List(U8), U64, U64, U64 -> U64
	tail = |bytes, i, stop, acc|
		if i >= stop {{ acc }} else {{
			b = U8.to_u64(List.get(bytes, i) ?? 0)
			Cce.tail(bytes, i + 1, stop, acc * 64 + U64.bitwise_and(b, 63))
		}}

	# `text-length`: the count of characters.
	length : Str -> I64
	length = |s| U64.to_i64_wrap(List.len(Cce.codes_of(s)))

	# `char-code-at`: the code of the i-th character, 0 past the end.
	at : Str, I64 -> I64
	at = |s, i| if i < 0 {{ 0 }} else {{ List.get(Cce.codes_of(s), I64.to_u64_wrap(i)) ?? 0 }}

	# `char-at` answers a character and refuses to run past the end.
	at_or_crash : Str, I64 -> I64
	at_or_crash = |s, i|
		if i < 0 {{ crash("char-at past the end") }}
		else {{ List.get(Cce.codes_of(s), I64.to_u64_wrap(i)) ?? crash("char-at past the end") }}

	# `char-to-text`, and what `show` of a Char prints.
	text : I64 -> Str
	text = |c| Str.from_utf8(Cce.utf8(Cce.to_point(c))) ?? ""

	to_point : I64 -> U64
	to_point = |c| if c < 0 or c > 127 {{ 0 }} else {{ List.get(Cce.points, I64.to_u64_wrap(c)) ?? 0 }}

	utf8 : U64 -> List(U8)
	utf8 = |p|
		if p < 128 {{ [U64.to_u8_wrap(p)] }}
		else if p < 2048 {{ [U64.to_u8_wrap(192 + U64.div_by(p, 64)), U64.to_u8_wrap(128 + U64.bitwise_and(p, 63))] }}
		else {{ [
			U64.to_u8_wrap(224 + U64.div_by(p, 4096)),
			U64.to_u8_wrap(128 + U64.bitwise_and(U64.div_by(p, 64), 63)),
			U64.to_u8_wrap(128 + U64.bitwise_and(p, 63)),
		] }}

	# `substring`, over characters.
	substring : Str, I64, I64 -> Str
	substring = |s, start, len| Cce.str_of(List.sublist(Cce.codes_of(s), {{ start: I64.to_u64_wrap(I64.max(start, 0)), len: I64.to_u64_wrap(I64.max(len, 0)) }}))

	str_of : List(I64) -> Str
	str_of = |cs| List.fold(cs, "", |acc, c| Str.concat(acc, Cce.text(c)))
}}
"#,
        codes = wrap(&codes),
        points = wrap(&pts)
    )
}
