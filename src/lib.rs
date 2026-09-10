//! A native Rust front end for Codex: `.codex` in, standard Codex IR out.
//! Lexer first; the ladder's rungs are the plan and they run lex, parse,
//! desugar, scope, check, lower in that order.

pub mod arity;
pub mod ast;
pub mod block;
pub mod builtins;
pub mod bump;
pub mod bundle;
pub mod charcode;
pub mod check;
pub mod cohesion;
pub mod cost;
pub mod code;
pub mod cst;
pub mod decl;
pub mod desugar;
pub mod effect_scope;
pub mod expr;
pub mod heapwatch;
pub mod interp;
pub mod ir;
pub mod lexer;
pub mod linearity;
pub mod ir_chapter;
pub mod ir_passes;
pub mod ir_text;
pub mod lambda_lifting;
pub mod lowering;
pub mod lowering_types;
pub mod parser;
pub mod preamble;
pub mod name_rules;
pub mod narrowing;
pub mod proof_norm;
pub mod punctual;
pub mod resolve_types;
pub mod scope;
pub mod scoper;
pub mod seams;
pub mod symbol;
pub mod pattern;
pub mod token;
pub mod typedef;
pub mod types;
pub mod xref;
