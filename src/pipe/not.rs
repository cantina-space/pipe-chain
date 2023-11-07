use crate::{Pipe, Result};
use fatal_error::FatalError;
use std::{fmt::Debug, marker::PhantomData};

/// Changes error behaviour
pub trait NotExt<I, O, E, R> {
    /// Fails if the given pipe succeeds
    fn not(self) -> Not<O, R, Self>
    where
        I: Clone,
        O: Debug,
        Self: Sized,
    {
        Not::new(self)
    }
}

impl<I, O, E, R, P> NotExt<I, O, E, R> for P where P: Pipe<I, O, E, R> {}

/// [NotExt::not] implementation
pub struct Not<O, R, P>(P, PhantomData<O>, PhantomData<R>);

impl<O, R, P> Not<O, R, P> {
    fn new(p: P) -> Self { Not(p, PhantomData, PhantomData) }
}

/// A pipe that should have failed succeed
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NotError<T, E> {
    /// The error succeeded
    Not(T),
    /// A fatal error occured
    Fatal(E),
}

impl<T, E> NotError<T, E> {
    /// unwrap the successfull result
    /// panics if `self` is [NotError::Fatal]
    pub fn unwrap_not(self) -> T
    where
        E: Debug,
    {
        match self {
            NotError::Not(x) => x,
            NotError::Fatal(x) => panic!("not error encountered a fatal error: {x:?}"),
        }
    }
}

impl<T: std::fmt::Debug, E: std::fmt::Display> std::fmt::Display for NotError<T, E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NotError::Not(x) => write!(f, "Not pipe succeeded: {x:?}"),
            NotError::Fatal(x) => write!(f, "Not pipe encountered a fatal error: '{x}'"),
        }
    }
}

impl<O: std::fmt::Debug, E: std::error::Error> std::error::Error for NotError<O, E> {}

impl<I, O, E, R, P> Pipe<I, (E,), NotError<(R, O), E>> for Not<O, R, P>
where
    I: Clone,
    P: Pipe<I, O, E, R>,
{
    fn apply(&mut self, input: I) -> Result<I, (E,), NotError<(R, O), E>> {
        match self.0.apply(input.clone()) {
            Ok(x) => Err(FatalError::Error(NotError::Not(x))),
            Err(x) if x.is_fatal() => Err(x.map(NotError::Fatal)),
            Err(x) => Ok((input, (x.into_inner(),))),
        }
    }
}
