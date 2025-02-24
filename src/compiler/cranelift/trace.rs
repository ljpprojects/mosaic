use crate::utils::Indirection;
use std::ops::Deref;

#[derive(Debug, Clone, PartialEq)]
pub enum ContextKind {
    Global,
    Function,
    CallArg,
    Return,
    Idx,
    Def,
    LeftOp(String),
    RightOp(String),
    FuncArg(String),
}

#[derive(Debug, Clone)]
pub struct Trace {
    pub parent: Option<Indirection<Trace>>,
    pub symbol: String,
    pub depth: usize,
    pub context: ContextKind,
}

impl Trace {
    pub fn new(
        parent: Option<Indirection<Trace>>,
        symbol: String,
        depth: usize,
        ctx: ContextKind,
    ) -> Self {
        Self {
            parent,
            symbol,
            depth,
            context: ctx,
        }
    }

    pub fn new_root(symbol: String) -> Self {
        Self {
            parent: None,
            symbol,
            depth: 0,
            context: ContextKind::Global,
        }
    }

    pub fn root(&self) -> Trace {
        let Some(cur) = self.parent.clone() else {
            return self.clone();
        };

        let mut cur = cur.deref();

        while let Some(indirection) = &cur.parent {
            cur = indirection;
        }

        cur.clone()
    }

    pub fn symbol(&self) -> &String {
        &self.symbol
    }

    pub fn depth(&self) -> usize {
        self.depth
    }

    pub fn nested(&self, symbol: String, ctx: ContextKind) -> Self {
        let depth = self.depth + 1;

        Trace::new(Some(Indirection::new(self.clone())), symbol, depth, ctx)
    }

    pub fn nested_ctx(&self, ctx: ContextKind) -> Self {
        let symbol = self.symbol.clone();

        self.nested(symbol, ctx)
    }
}

/*
GLOBAL
  main
    if
      returned ← here
*/
