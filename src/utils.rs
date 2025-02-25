
pub trait IndirectionTrait<T> {
    fn map<U, F: FnOnce(&T) -> U>(self, f: F) -> Indirection<U>;
    fn map_option<U, F: FnOnce(&T) -> Option<U>>(self, f: F) -> Option<Indirection<U>>;
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
}

#[must_use = "This function should be used sparingly."]
pub struct UseSparingly<T>(T);

impl<T> UseSparingly<T> {
    pub(crate) fn new(t: T) -> UseSparingly<T> {
        UseSparingly(t)
    }

    pub fn acknowledge(self) -> T {
        self.0
    }
}

impl<T> From<T> for UseSparingly<T> {
    fn from(t: T) -> Self {
        UseSparingly(t)
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
            _ => panic!("unwrapped left value on right or centre value")
        }
    }

    pub fn unwrap_centre(self) -> B {
        match self {
            Self::Centre(v) => v,
            _ => panic!("unwrapped left value on right or left value")
        }
    }

    pub fn unwrap_right(self) -> C {
        match self {
            Self::Right(v) => v,
            _ => panic!("unwrapped left value on left or centre value")
        }
    }
}