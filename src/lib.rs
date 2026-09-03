//! A native Rust front end for Codex: `.codex` in, standard Codex IR out.
//! Lexer first; the ladder's rungs are the plan and they run lex, parse,
//! desugar, scope, check, lower in that order.

pub mod ast;
pub mod block;
pub mod builtins;
pub mod charcode;
pub mod cohesion;
pub mod cst;
pub mod decl;
pub mod desugar;
pub mod expr;
pub mod interp;
pub mod lexer;
pub mod parser;
pub mod preamble;
pub mod scope;
pub mod seams;
pub mod pattern;
pub mod token;
pub mod typedef;
pub mod types;
pub mod xref;
