//! Capability scope -- upstream's `Section: Capability Scope` and
//! `Section: Capability Checker` (TypeChecker.codex:972, :4420).
//!
//! A signature may grant an effect over a SCOPE: `FileSystem.Read
//! "/config/"`, `Network.Read "api.example.com:443"`, `Console.Write
//! "stdout"`. Inside a definition with any scoped grant, a call to an
//! operation that names a resource must stay inside the grant (CDX4002):
//! a path grant is a prefix, a network grant is an authority (host, and the
//! port when both name one), a console grant is a channel. A callee's own
//! declared scopes must sit inside the caller's grants too. And `opening`
//! may declare only effects the manifest can carry (CDX4001).

use crate::ast::{Expr, LiteralKind};
use crate::check::{strip_forall, Cdx, Ty, TyEnv, UnifyState};

/// A grant or a label: the effect's name and its scope, `""` for none.
pub type Label = (String, String);

/// `capability-names`, from `foreword/core/Capability`.
const CAPABILITY_NAMES: &[&str] = &[
    "Console", "FileSystem", "Network", "Concurrent", "Device", "Gpu.Compute", "Gpu.Memory", "Identity",
    "Capability", "Gpu", "Camera", "Microphone", "Location", "Sensors", "Display", "Flash", "Audio",
    "Process", "Gpio", "Uart", "Spi", "I2c", "Adc", "Power", "Rng",
];

/// `cap-name-covered`: the name, or its head before the dot.
fn cap_name_covered(eff: &str) -> bool {
    if CAPABILITY_NAMES.contains(&eff) {
        return true;
    }
    match eff.find('.') {
        Some(dot) => CAPABILITY_NAMES.contains(&&eff[..dot]),
        None => false,
    }
}

/// `collect-effect-names`: every effect an arrow or an effectful type names.
fn collect_effect_labels(t: &Ty, env: &TyEnv<'_>) -> Vec<Label> {
    match t {
        Ty::Fun(_, row, r) => {
            let mut out: Vec<Label> = row.labels.clone();
            out.extend(collect_effect_labels(r, env));
            out
        }
        Ty::ForAll(_, b) | Ty::ForAllEff(_, b) => collect_effect_labels(b, env),
        Ty::Effectful(effs, scopes, inner) => {
            let mut out: Vec<Label> = effs
                .iter()
                .enumerate()
                .map(|(i, e)| (env.syms.text(*e).to_string(), scopes.get(i).cloned().unwrap_or_default()))
                .collect();
            out.extend(collect_effect_labels(inner, env));
            out
        }
        _ => Vec::new(),
    }
}

/// `check-opening-capabilities`: `opening`'s effects against the vocabulary.
pub fn check_opening_capabilities(env: &TyEnv<'_>, st: &mut UnifyState) {
    let Some(sym) = env.syms.find("opening") else { return };
    let Some(t) = env.get(sym) else { return };
    let labels = collect_effect_labels(t, env);
    // Upstream builds the list back to front, so the errors come out last
    // effect first.
    for (name, _) in labels.iter().rev() {
        if !cap_name_covered(name) {
            st.error(Cdx::CAPABILITY_NOT_GRANTED, format!("Effect '{name}' has no capability the manifest can carry"));
        }
    }
}

// ---------------------------------------------------------------------------
// Scopes.

/// `scoped-op-effect`: the operations whose argument is a resource.
fn scoped_op_effect(n: &str) -> &'static str {
    match n {
        "read-file" | "read-file-raw" | "read-file-uni" | "read-text" | "file-exists" => "FileSystem.Read",
        "write-file" => "FileSystem.Write",
        "fetch" | "resolve-dns" => "Network.Read",
        "post" => "Network.Write",
        _ => match console_channel_op(n) {
            "" => "",
            "stdin" => "Console.Read",
            _ => "Console.Write",
        },
    }
}

/// `console-channel-op`: the channel a console operation is fixed to.
fn console_channel_op(n: &str) -> &'static str {
    match n {
        "print-line" | "print-line-raw" | "print-text" | "print-line-uni" | "print-uni" => "stdout",
        "print-error" | "print-error-uni" => "stderr",
        "read-line" | "read-line-cce" | "read-key" => "stdin",
        _ => "",
    }
}

fn effect_covered_by(declared: &str, body_eff: &str) -> bool {
    declared == body_eff || body_eff.find('.').is_some_and(|dot| declared == &body_eff[..dot])
}

fn auth_host(a: &str) -> &str {
    a.split(':').next().unwrap_or("")
}

fn auth_port(a: &str) -> &str {
    a.find(':').map_or("", |p| &a[p + 1..])
}

/// `authority-admits`: a resource that names no port is a hostname, which
/// never reaches a port.
fn authority_admits(grant: &str, res: &str) -> bool {
    if auth_host(grant) != auth_host(res) {
        return false;
    }
    let (gp, rp) = (auth_port(grant), auth_port(res));
    gp.is_empty() || rp.is_empty() || gp == rp
}

/// `scope-admits`, by the effect's kind of scope.
fn scope_admits(eff: &str, grant: &str, res: &str) -> bool {
    if eff.starts_with("Network") {
        authority_admits(grant, res)
    } else if eff.starts_with("Console") {
        res == grant
    } else {
        res.starts_with(grant)
    }
}

/// `url-authority`: the authority a URL names, with the scheme's port when
/// the URL leaves it implicit.
fn url_authority(u: &str) -> String {
    let start = u.find("://").map_or(0, |i| i + 3);
    let rest = &u[start..];
    let auth = rest.split('/').next().unwrap_or("");
    if auth.contains(':') {
        auth.to_string()
    } else {
        format!("{auth}:{}", if u.starts_with("https") { "443" } else { "80" })
    }
}

fn op_resource(eff: &str, v: &str) -> String {
    if eff.starts_with("Network") {
        url_authority(v)
    } else {
        v.to_string()
    }
}

fn effect_has_grant(grants: &[Label], eff: &str) -> bool {
    grants.iter().any(|(n, _)| effect_covered_by(n, eff))
}

/// `scope-permits`: some grant covering the effect admits the resource,
/// an unscoped grant admitting everything.
fn scope_permits(grants: &[Label], eff: &str, res: &str) -> bool {
    grants.iter().any(|(n, scope)| effect_covered_by(n, eff) && (scope.is_empty() || scope_admits(eff, scope, res)))
}

/// `lint-effect-scope`, at every application whose callee is a name.
pub fn lint_effect_scope(func: &Expr, arg: &Expr, env: &TyEnv<'_>, st: &mut UnifyState) {
    if !st.scope_grants.iter().any(|(_, s)| !s.is_empty()) {
        return;
    }
    let Expr::NameRef(n, _) = func else { return };
    let fname = env.syms.text(*n).to_string();
    let grants = st.scope_grants.clone();
    let eff = scoped_op_effect(&fname);
    if eff.is_empty() {
        lint_callee_scopes(&grants, &fname, env, st);
        return;
    }
    let channel = console_channel_op(&fname);
    if !channel.is_empty() {
        // `lint-fixed-resource`.
        if effect_has_grant(&grants, eff) && !scope_permits(&grants, eff, channel) {
            st.error(
                Cdx::SCOPE_VIOLATION,
                format!("'{fname}' uses the \"{channel}\" channel, which is outside the scope this signature grants for {eff}."),
            );
        }
        return;
    }
    // `lint-scoped-op`.
    if !effect_has_grant(&grants, eff) {
        return;
    }
    match arg {
        Expr::Lit(v, LiteralKind::TextLit, _) => {
            if !scope_permits(&grants, eff, &op_resource(eff, v)) {
                st.error(
                    Cdx::SCOPE_VIOLATION,
                    format!("'{fname}' names \"{v}\", which is outside the scope this signature grants for {eff}."),
                );
            }
        }
        Expr::Lit(..) => {}
        _ => st.error(
            Cdx::SCOPE_VIOLATION,
            format!("'{fname}' is given a computed resource, so the compiler cannot prove it stays inside the scope this signature grants for {eff}. Pass a literal, or widen the declared scope."),
        ),
    }
}

/// `lint-callee-scopes`: a callee's declared scopes sit inside the grants.
fn lint_callee_scopes(grants: &[Label], fname: &str, env: &TyEnv<'_>, st: &mut UnifyState) {
    let Some(sym) = env.syms.find(fname) else { return };
    let Some(t) = env.get(sym) else { return };
    let labels = collect_effect_labels(&strip_forall(t), env);
    for (eff, scope) in &labels {
        if !effect_has_grant(grants, eff) || scope_permits(grants, eff, scope) {
            continue;
        }
        if scope.is_empty() {
            st.error(
                Cdx::SCOPE_VIOLATION,
                format!("'{fname}' performs {eff} with no scope of its own, so it may touch anything, and this signature grants {eff} only over a narrower scope. Declare the scope on '{fname}', or widen the grant."),
            );
        } else {
            st.error(
                Cdx::SCOPE_VIOLATION,
                format!("'{fname}' is declared over the scope \"{scope}\" for {eff}, which is not inside the scope this signature grants. A scope may narrow, never widen."),
            );
        }
        return;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_url_names_its_authority_with_the_schemes_port() {
        assert_eq!(url_authority("https://api.example.com/v1/status"), "api.example.com:443");
        assert_eq!(url_authority("https://api.example.com:4433/v1/status"), "api.example.com:4433");
        assert_eq!(url_authority("http://host/x"), "host:80");
    }

    #[test]
    fn a_scope_admits_by_its_kind() {
        assert!(scope_admits("FileSystem.Read", "/config/", "/config/app.txt"));
        assert!(!scope_admits("FileSystem.Read", "/config/", "/etc/passwd"));
        assert!(scope_admits("Network.Read", "api.example.com", "api.example.com:443"));
        assert!(!scope_admits("Network.Read", "api.example.com:443", "api.example.com:4433"));
        assert!(!scope_admits("Network.Read", "api.example.com", "api.example.com.evil.net:443"));
        assert!(!scope_admits("Console.Write", "stdout", "stderr"));
    }
}
