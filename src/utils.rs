use std::fmt::{Debug, Display};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;
use std::rc::Rc;

pub enum OneOf<A, B> {
    First(A),
    Second(B),
}

impl<A: Display, B: Display> Display for OneOf<A, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OneOf::First(a) => write!(f, "{}", a),
            OneOf::Second(b) => write!(f, "{}", b),
        }
    }
}

impl<A: Debug, B: Debug> Debug for OneOf<A, B> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OneOf::First(a) => write!(f, "{:?}", a),
            OneOf::Second(b) => write!(f, "{:?}", b),
        }
    }
}

impl<A, B> OneOf<A, B> {
    pub fn unwrap_as_first(self) -> A {
        match self {
            OneOf::First(a) => a,
            OneOf::Second(_) => panic!("called `Either::unwrap_as_a()` on a `B`"),
        }
    }

    pub fn unwrap_as_second(self) -> B {
        match self {
            OneOf::First(_) => panic!("called `Either::unwrap_as_b()` on an `A`"),
            OneOf::Second(b) => b,
        }
    }

    pub fn unwrap_as_first_or_default(self, default: A) -> A {
        match self {
            OneOf::First(a) => a,
            OneOf::Second(_) => default,
        }
    }

    pub fn unwrap_as_second_or_default(self, default: B) -> B {
        match self {
            OneOf::First(_) => default,
            OneOf::Second(b) => b,
        }
    }

    pub fn into_first(self) -> Option<A> {
        match self {
            OneOf::First(a) => Some(a),
            OneOf::Second(_) => None,
        }
    }

    pub fn into_second(self) -> Option<B> {
        match self {
            OneOf::First(_) => None,
            OneOf::Second(b) => Some(b),
        }
    }

    pub fn as_first(&self) -> Option<&A> {
        match self {
            OneOf::First(a) => Some(a),
            OneOf::Second(_) => None,
        }
    }

    pub fn as_second(&self) -> Option<&B> {
        match self {
            OneOf::First(_) => None,
            OneOf::Second(b) => Some(b),
        }
    }
}

pub struct MutRc<T> {
    ptr: NonNull<MutRcInner<T>>,
    phantom: PhantomData<MutRcInner<T>>,
}

struct MutRcInner<T> {
    rc: usize,
    data: T,
}

impl<T> MutRc<T> {
    pub fn new(data: T) -> MutRc<T> {
        let boxed = Box::new(MutRcInner { rc: 1usize, data });

        MutRc {
            ptr: NonNull::new(Box::into_raw(boxed)).unwrap(),
            phantom: PhantomData,
        }
    }

    pub fn into_mut<'a>(mut self) -> &'a mut T {
        let inner = unsafe { self.ptr.as_mut() };

        &mut inner.data
    }

    pub fn as_mut(&mut self) -> &mut T {
        let inner = unsafe { self.ptr.as_mut() };

        &mut inner.data
    }

    pub fn as_ref(&self) -> &T {
        let inner = unsafe { self.ptr.as_ref() };

        &inner.data
    }

    pub fn borrow_mut(&self) -> &mut T {
        let inner = unsafe { self.ptr.as_ptr().as_mut() }.unwrap();

        &mut inner.data
    }

    pub fn get(self) -> T {
        let inner = unsafe { self.ptr.read() };

        inner.data
    }
}

impl<T> Deref for MutRc<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl<T> DerefMut for MutRc<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut()
    }
}

impl<T> Clone for MutRc<T> {
    fn clone(&self) -> Self {
        let inner = unsafe {
            (self as *const Self as *mut Self)
                .as_mut()
                .unwrap()
                .ptr
                .as_mut()
        };

        if inner.rc >= isize::MAX as usize {
            std::process::abort();
        }

        Self {
            ptr: self.ptr,
            phantom: PhantomData,
        }
    }
}

pub trait IndirectionTrait<T> {
    fn map<U, F: FnOnce(&T) -> U>(self, f: F) -> Indirection<U>;
}

pub type Indirection<T> = Rc<T>;

impl<T> IndirectionTrait<T> for Indirection<T> {
    fn map<U, F: FnOnce(&T) -> U>(self, f: F) -> Indirection<U> {
        let res = f(self.as_ref());

        Indirection::new(res)
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
