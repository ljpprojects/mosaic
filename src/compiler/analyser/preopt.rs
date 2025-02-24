//! This is the module for Mosaic's pre-compilation-optimisations (or pre-opts)
//! ## List of every pre-opt
//! **Unused definitions**
//! ```python
//! let foo: i32 = 65 # automatically removed
//! ```
//! **Mutable demotion**
//! ```bash
//! mut foo: i32 = 47 # demoted to a let statement
//!
//! bar(foo + 8)
//! ```
//! **Automatic constant-ing**
//! ```ruby
//! let pi: f64 = 3.14 # converted to a const statement
//!
//! println("\{pi}")
//! ```
//! **If folding**
//! ```
//! # inlined to printf(...)
//! if true {
//!     printf("%b\n", true)
//! }
//! ```
//!

use crate::compiler::analyser;
use crate::compiler::analyser::UsageKind;
use crate::parser::{AstNode, ParseBlock};

pub struct PreoptEngine<'a> {
    code: &'a [AstNode],
    buffer: Vec<AstNode>,
}

impl<'a> PreoptEngine<'a> {
    pub fn new(code: &'a [AstNode]) -> PreoptEngine<'a> {
        PreoptEngine {
            code,
            buffer: Vec::from(code),
        }
    }

    pub fn finish(self) -> Box<[AstNode]> {
        self.buffer.into_boxed_slice()
    }

    pub fn removed_unused_defs(&mut self) {
        let mut i = 0usize;

        while let Some(node) = self.buffer.get_mut(i) {
            let name = match node {
                AstNode::FnStmt {
                    code: ParseBlock::Plain(code),
                    ..
                } => {
                    let mut engine = PreoptEngine::new(code);
                    engine.removed_unused_defs();

                    *code = engine.finish();

                    i += 1;
                    continue;
                }
                AstNode::LetStmt { name, .. } => name,
                AstNode::MutStmt { name, .. } => name,
                _ => {
                    i += 1;
                    continue;
                }
            };

            let usages = analyser::get_usages_of(&name, &self.code[i..]);

            if usages.len() < 2 {
                self.buffer.remove(i);
            } else {
                i += 1;
            }
        }
    }

    pub fn demote_mutables(&mut self) {
        let mut i = 0usize;

        while let Some(node) = self.buffer.get_mut(i) {
            let (name, def_type, value) = match node {
                AstNode::FnStmt {
                    code: ParseBlock::Plain(code),
                    ..
                } => {
                    let mut engine = PreoptEngine::new(code);
                    engine.demote_mutables();

                    *code = engine.finish();

                    i += 1;
                    continue;
                }
                AstNode::LetStmt {
                    name,
                    def_type,
                    value,
                } => (name, def_type, value),
                AstNode::MutStmt {
                    name,
                    def_type,
                    value,
                } => (name, def_type, value),
                _ => {
                    i += 1;
                    continue;
                }
            };

            let usages = analyser::get_usages_of(&name, &self.code[i..])
                .into_iter()
                .filter(|u| u.kind == UsageKind::Assignment || u.kind == UsageKind::MakePointer)
                .collect::<Vec<_>>();

            if usages.len() == 0 {
                let demoted = AstNode::LetStmt {
                    name: name.clone(),
                    def_type: def_type.clone(),
                    value: value.clone(),
                };

                *node = demoted
            }

            i += 1;
        }
    }
}
