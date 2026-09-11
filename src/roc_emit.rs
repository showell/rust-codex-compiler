//! Roc from the IR: the definitions the driver would emit for a unit, spelled
//! as one Roc program for Roc's default Echo platform.
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

const KEYWORDS: [&str; 18] = [
    "and", "as", "crash", "dbg", "else", "expect", "exposing", "for", "if", "import", "in",
    "match", "module", "or", "return", "var", "where", "while",
];

/// A constant with this many literal leaves is a data table, baked elsewhere.
pub const BAKED_AT: usize = 256;

fn leaf_literals(e: &IrExpr) -> usize {
    let mut n = 0;
    e.walk(&mut |x| {
        if matches!(x, IrExpr::IntLit(..) | IrExpr::NumLit(..) | IrExpr::TextLit(..) | IrExpr::BoolLit(..)) {
            n += 1;
        }
    });
    n
}

/// The whole unit as ONE Roc program, for the default Echo platform.
pub fn emit_program(
    ch: &Chapter,
    tds: &TypeDefs,
    syms: &SymTab,
    defs: &[IrDef],
) -> Result<String, String> {
    let mut cx = Cx::new(ch, tds, syms, defs, false);
    let mut body = String::new();
    let mut slug = String::new();
    let mut main = None;
    for d in defs {
        if syms.text(d.name) == "opening" {
            main = Some(cx.opening(d)?);
            continue;
        }
        if d.origin != slug {
            slug = d.origin.clone();
            body.push_str(&format!("\n# --- {slug} ---\n"));
        }
        body.push('\n');
        body.push_str(&cx.def_or_baked(d, 0)?);
    }
    let Some(main) = main else {
        return Err("no opening: nothing to run".into());
    };
    let mut out = format!(
        "# {} -- emitted from Codex by rocemit (rust-codex-compiler). Do not edit.\n\n",
        ch.chapter_title
    );
    // `Maybe` is a language type the checker knows without a declaration
    // (`ctd`); a unit that cites the chapter declaring it carries its own.
    if !cx.type_module.contains_key(&cx.maybe) {
        out.push_str("Maybe(a) : [None, Just(a)]\n");
    }
    for td in &ch.type_defs {
        out.push_str(&cx.type_def(td, 0)?);
    }
    if cx.uses_line {
        out.push_str(LINE_HELPER);
    }
    out.push_str(&body);
    out.push_str("\n# --- Entry ---\n\n");
    out.push_str(&main);
    Ok(out)
}

const LINE_HELPER: &str =
    "\n# The Echo platform's echo! writes no newline; a Codex line is one.\nline! = |s| echo!(Str.concat(s, \"\\n\"))\n";

/// The unit as Roc TYPE MODULES, one per Codex chapter, and one app for the
/// chapter that holds `opening`: `(<file name>, <text>)` pairs.
///
/// A chapter becomes a void module, `Slug :: [].{ ... }`, whose associated
/// items are the chapter's type definitions and definitions; another module
/// reaches them as `Slug.name`. Roc's module documentation recommends
/// exactly this shape for a namespace of functions, and it is what lets the
/// screensaver itself import the same chapters the specs grade.
///
/// A baked constant is a forwarder to `<Slug>Data.name`, a module the stills
/// baker writes; the app is the spec's own definitions and `main!`.
pub fn emit_modules(
    ch: &Chapter,
    tds: &TypeDefs,
    syms: &SymTab,
    defs: &[IrDef],
) -> Result<Vec<(String, String)>, String> {
    let mut cx = Cx::new(ch, tds, syms, defs, true);
    let Some(app) = defs.iter().find(|d| syms.text(d.name) == "opening") else {
        return Err("no opening: nothing to run".into());
    };
    let app_slug = app.origin.clone();
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
            if syms.text(d.name) == "opening" {
                main = Some(cx.opening(d)?);
                continue;
            }
            items.push('\n');
            items.push_str(&cx.def_or_baked(d, base)?);
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
    if prelude {
        files.push((
            "Prelude.roc".into(),
            "# Prelude -- the language types no chapter declares.\n\nPrelude :: [].{\n\tMaybe(a) : [None, Just(a)]\n}\n".into(),
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
    /// Every emitted definition and its parameter count: a call must be
    /// saturated, because Roc calls are.
    arity: BTreeMap<Sym, usize>,
    /// Which chapter each definition and each declared type lives in. Empty
    /// in the single-file layout, where nothing is qualified.
    def_module: BTreeMap<Sym, String>,
    type_module: BTreeMap<Sym, String>,
    modules: bool,
    maybe: Sym,
    /// The chapter being emitted, and the modules its text has reached for.
    current: String,
    imports: std::collections::BTreeSet<String>,
    /// Names bound by the enclosing parameters, lets and patterns.
    locals: Vec<Sym>,
    /// Type-variable letters, per definition signature.
    tvars: BTreeMap<u32, String>,
    uses_line: bool,
}

impl<'a> Cx<'a> {
    fn new(ch: &Chapter, tds: &'a TypeDefs, syms: &'a SymTab, defs: &[IrDef], modules: bool) -> Cx<'a> {
        let mut cx = Cx {
            syms,
            tds,
            arity: defs.iter().map(|d| (d.name, d.params.len())).collect(),
            def_module: BTreeMap::new(),
            type_module: BTreeMap::new(),
            modules,
            maybe: syms.find("Maybe").unwrap_or_default(),
            current: String::new(),
            imports: Default::default(),
            locals: Vec::new(),
            tvars: BTreeMap::new(),
            uses_line: false,
        };
        for (td, c) in ch.type_defs.iter().zip(&ch.type_def_chapters) {
            let n = match td {
                TypeDef::Record(n, ..) | TypeDef::Variant(n, ..) | TypeDef::Unit(n, ..) => *n,
            };
            cx.type_module.insert(n, c.clone());
        }
        if modules {
            for d in defs {
                cx.def_module.insert(d.name, d.origin.clone());
            }
        }
        cx
    }

    /// A name from module `module`, as seen from the module being emitted:
    /// bare at home, `Module.name` elsewhere, and the import is remembered.
    fn qualified(&mut self, module: &str, name: String) -> String {
        if !self.modules || module.is_empty() || module == self.current {
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
        let name = self.syms.text(n).to_string();
        let m = match self.type_module.get(&n) {
            Some(m) => m.clone(),
            None if self.modules && n == self.maybe => "Prelude".to_string(),
            None => String::new(),
        };
        if !self.modules || m.is_empty() {
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
        let collides = self.arity.contains_key(&n)
            && (!self.modules || self.def_module.get(&n).is_some_and(|m| *m == self.current));
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

    fn ty(&mut self, t: &Ty) -> Result<String, String> {
        Ok(match t {
            Ty::Integer(..) => "I64".into(),
            Ty::Real(RealWidth::F64, _) => "F64".into(),
            Ty::Text => "Str".into(),
            Ty::Boolean => "Bool".into(),
            Ty::Nothing => "{}".into(),
            Ty::List(e) => format!("List({})", self.ty(e)?),
            Ty::Fun(..) => {
                let (ps, r) = self.fun_parts(t)?;
                format!("({} -> {})", ps.join(", "), r)
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
        let mut cur = t;
        loop {
            match cur {
                Ty::Fun(p, _, r) => {
                    ps.push(self.ty(p)?);
                    cur = r;
                }
                Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => cur = b,
                _ => break,
            }
        }
        Ok((ps, self.ty(cur)?))
    }

    /// A definition's signature: `k` parameters peel `k` arrows.
    fn signature(&mut self, d: &IrDef) -> Result<String, String> {
        self.tvars.clear();
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
        let r = self.ty(cur)?;
        Ok(if ps.is_empty() { r } else { format!("{} -> {}", ps.join(", "), r) })
    }

    fn texpr(&mut self, t: &TypeExpr) -> Result<String, String> {
        Ok(match t {
            TypeExpr::Named(n, _) => match self.syms.text(*n) {
                "Real" => "F64".into(),
                "Integer" => "I64".into(),
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
            _ => return Err("a type form outside the subset in a type definition".into()),
        })
    }

    fn type_def(&mut self, td: &TypeDef, base: usize) -> Result<String, String> {
        let syms = self.syms;
        let head = |n: Sym, ps: &[Sym]| -> Result<String, String> {
            let name = syms.text(n).to_string();
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
                if fs.is_empty() {
                    format!("{tabs}{} : {{}}\n", head(*n, ps)?)
                } else {
                    format!("{tabs}{} : {{ {} }}\n", head(*n, ps)?, fs.join(", "))
                }
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
                format!("{tabs}{} : [{}]\n", head(*n, ps)?, cs.join(", "))
            }
            TypeDef::Unit(n, ..) => return Err(format!("unit type `{}`", self.syms.text(*n))),
        })
    }

    // ---- definitions ----------------------------------------------------

    /// A definition, or the line that says a data table was left to a baker.
    ///
    /// **A DATA TABLE IS NOT EMITTED, AND THE OMISSION IS WRITTEN DOWN.**
    /// Roc's checker is superlinear in the literal elements of a FILE
    /// (measured: 1k, 2k, 4k points check in 3.6, 9.9, 31 seconds, as
    /// records or as floats, in one list or many) and the same data as a
    /// string checks in half a second. So a constant that is a literal of
    /// BAKED_AT or more leaves is left to a baker that spells it as a
    /// string. In the single-file layout the line names it and the driver
    /// appends the baked text; in the module layout it forwards to
    /// `<Slug>Data.name`, the module the baker writes. Either way a missing
    /// baked name is Roc's undefined-name error, never a silent hole.
    fn def_or_baked(&mut self, d: &IrDef, base: usize) -> Result<String, String> {
        let leaves = leaf_literals(&d.body);
        if !d.params.is_empty() || leaves < BAKED_AT {
            return self.def(d, base);
        }
        let sig = self.signature(d)?;
        let name = self.ident(d.name)?;
        let tabs = "\t".repeat(base);
        let mut out = format!("{tabs}# baked: {name} : {sig} -- {} {leaves} literals\n", d.origin);
        if self.modules {
            let data = format!("{}Data", d.origin);
            let from = self.qualified(&data, name.clone());
            out.push_str(&format!("{tabs}{name} : {sig}\n{tabs}{name} = {from}\n"));
        }
        Ok(out)
    }

    fn def(&mut self, d: &IrDef, base: usize) -> Result<String, String> {
        let name = self.ident(d.name)?;
        let sig = self.signature(d)?;
        let mark = self.locals.len();
        let mut ps = Vec::new();
        for p in &d.params {
            self.locals.push(p.name);
            ps.push(self.binder(p.name, &[&d.body])?);
        }
        let body = self.expr(&d.body, base)?;
        self.locals.truncate(mark);
        let tabs = "\t".repeat(base);
        Ok(if ps.is_empty() {
            format!("{tabs}{name} : {sig}\n{tabs}{name} = {body}\n")
        } else {
            format!("{tabs}{name} : {sig}\n{tabs}{name} = |{}| {body}\n", ps.join(", "))
        })
    }

    /// `opening : [Console] Nothing = act ...` is `main!`.
    fn opening(&mut self, d: &IrDef) -> Result<String, String> {
        let IrExpr::Act(stmts, _, _) = &d.body else {
            return Err("opening is not an act".into());
        };
        if !d.params.is_empty() {
            return Err("opening takes parameters".into());
        }
        let mut out = String::from("main! = |_args| {\n");
        let mark = self.locals.len();
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
        Ok(match e {
            E::IntLit(v, _) => int_lit(*v),
            E::NumLit(bits, _) => num_lit(*bits),
            E::TextLit(s, _) => roc_quote(s),
            E::BoolLit(b, _) => if *b { "True".into() } else { "False".into() },
            E::CharLit(..) => return Err("char literal".into()),
            E::Name(n, _, _) => self.name_value(*n)?,
            E::Binary(op, l, r, _, _) => {
                let (l, r) = (self.expr(l, ind)?, self.expr(r, ind)?);
                self.binary(*op, l, r)?
            }
            E::Negate(x, _, _) => format!("(-{})", self.expr(x, ind)?),
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
        if self.locals.contains(&n) {
            return self.local(n);
        }
        if self.arity.contains_key(&n) {
            return self.def_ref(n);
        }
        let t = self.syms.text(n);
        if t.starts_with(|c: char| c.is_ascii_uppercase()) {
            return self.tag(n);
        }
        Err(format!("builtin `{t}` used as a value"))
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

    fn binary(&self, op: IrBinOp, l: String, r: String) -> Result<String, String> {
        use IrBinOp as B;
        Ok(match op {
            B::AddInt | B::AddNum => format!("({l} + {r})"),
            B::SubInt | B::SubNum => format!("({l} - {r})"),
            B::MulInt | B::MulNum => format!("({l} * {r})"),
            B::DivNum => format!("({l} / {r})"),
            B::DivInt => format!("I64.div_trunc_by({l}, {r})"),
            B::RemInt => format!("I64.rem_by({l}, {r})"),
            B::PowInt => format!("I64.pow({l}, {r})"),
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
            B::ApproxEqExact => format!("(F64.to_bits({l}) == F64.to_bits({r}))"),
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
        let text = self.syms.text(*n).to_string();
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
        Ok(match name {
            "list-length" => {
                want(1)?;
                format!("U64.to_i64_wrap(List.len({}))", xs[0])
            }
            "list-at" => {
                want(2)?;
                format!("(List.get({}, I64.to_u64_wrap({})) ?? crash(\"list-at out of range\"))", xs[0], xs[1])
            }
            "list-push" | "list-snoc" => {
                want(2)?;
                format!("List.append({}, {})", xs[0], xs[1])
            }
            "show" | "integer-to-text" => {
                want(1)?;
                if !matches!(args[0].ty(), Ty::Integer(..)) {
                    return Err(format!("show on a {}", crate::ir_text::render_ty(self.syms, &args[0].ty())));
                }
                format!("I64.to_str({})", xs[0])
            }
            "real-from-int" => {
                want(1)?;
                format!("I64.to_f64({})", xs[0])
            }
            "real-to-int" => {
                want(1)?;
                format!("F64.to_i64_wrap({})", xs[0])
            }
            "real-abs" => {
                want(1)?;
                format!("F64.abs({})", xs[0])
            }
            "real-sqrt" => {
                want(1)?;
                format!("F64.sqrt({})", xs[0])
            }
            "real-max" => {
                want(2)?;
                format!("F64.max({}, {})", xs[0], xs[1])
            }
            "real-min" => {
                want(2)?;
                format!("F64.min({}, {})", xs[0], xs[1])
            }
            "real-to-bits" => {
                want(1)?;
                format!("U64.to_i64_wrap(F64.to_bits({}))", xs[0])
            }
            "bits-to-real" => {
                want(1)?;
                format!("F64.from_bits(I64.to_u64_wrap({}))", xs[0])
            }
            "bit-and" => {
                want(2)?;
                format!("I64.bitwise_and({}, {})", xs[0], xs[1])
            }
            "bit-or" => {
                want(2)?;
                format!("I64.bitwise_or({}, {})", xs[0], xs[1])
            }
            "bit-xor" => {
                want(2)?;
                format!("I64.bitwise_xor({}, {})", xs[0], xs[1])
            }
            "bit-not" => {
                want(1)?;
                format!("I64.bitwise_not({})", xs[0])
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
                Ty::Integer(..) => v.clone(),
                Ty::Text => roc_quote(v),
                Ty::Boolean => if v == "true" { "True".into() } else { "False".into() },
                other => return Err(format!("literal pattern of type {}", crate::ir_text::render_ty(self.syms, other))),
            },
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
fn num_lit(bits: i64) -> String {
    let f = f64::from_bits(bits as u64);
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
