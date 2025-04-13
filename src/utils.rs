#[macro_export]
macro_rules! ternary {
    ($cond: expr => $y: expr; $n: expr) => {
        if $cond { $y } else { $n }
    };
}

pub trait IndirectionTrait<T> {
    fn map<U, F: FnOnce(&T) -> U>(self, f: F) -> Indirection<U>;
    fn map_option<U, F: FnOnce(&T) -> Option<U>>(self, f: F) -> Option<Indirection<U>>;
    fn map_err<U, E, F: FnOnce(&T) -> Result<U, E>>(self, f: F) -> Result<Indirection<U>, E>;
}

pub type Indirection<T> = Box<T>;

impl<T> IndirectionTrait<T> for Indirection<T> {
    fn map<U, F: FnOnce(&T) -> U>(self, f: F) -> Indirection<U> {
        let res = f(self.as_ref());

        Indirection::new(res)
    }

    fn map_option<U, F: FnOnce(&T) -> Option<U>>(self, f: F) -> Option<Indirection<U>> {
        let res = f(self.as_ref())?;

        Some(Indirection::new(res))
    }

    fn map_err<U, E, F: FnOnce(&T) -> Result<U, E>>(self, f: F) -> Result<Indirection<U>, E> {
        let res = f(self.as_ref())?;

        Ok(Indirection::new(res))
    }
}

pub enum OneOf<A, B, C> {
    Left(A),
    Centre(B),
    Right(C)
}

impl<A, B, C> OneOf<A, B, C> {
    pub fn unwrap_left(self) -> A {
        match self {
            Self::Left(v) => v,
            _ => panic!("Attempted to unwrap left (A) value on a right (C) or centre value (B)")
        }
    }

    pub fn unwrap_centre(self) -> B {
        match self {
            Self::Centre(v) => v,
            _ => panic!("Attempted to unwrap the centre (B) value on a right (C) or left (A) value")
        }
    }

    pub fn unwrap_right(self) -> C {
        match self {
            Self::Right(v) => v,
            _ => panic!("Attempted to unwrap the right (C) value on a left (A) or centre (B) value")
        }
    }
}