//! A native Rust front end for Codex: `.codex` in, standard Codex IR out.
//! Lexer first; the ladder's rungs are the plan and they run lex, parse,
//! desugar, scope, check, lower in that order.

pub mod charcode;
pub mod cst;
pub mod expr;
pub mod lexer;
pub mod parser;
pub mod pattern;
pub mod token;
pub mod types;
