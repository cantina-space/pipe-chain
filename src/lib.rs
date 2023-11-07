#![feature(round_char_boundary)]
#![warn(missing_docs)]
#![doc = include_str!("../readme.md")]

pub mod byte;
pub mod parser;
pub mod pipe;
pub mod str;
mod tag;
mod take;

pub use self::{pipe::*, tag::*, take::*};
use fatal_error::{FatalError, NeverErr};

/// Convenience type to simplify the signature of pipe result types
///
/// `R`: remaining input
///
/// `O`: Output
///
/// `E`: an error wrapped into a FatalError
pub type Result<R, O, E> = std::result::Result<(R, O), FatalError<E>>;

/// Combinator trait
pub trait Pipe<I, O, E = NeverErr, R = I> {
    /// Produces a [Result] from an input
    ///
    /// from an input `I` produces either:
    ///
    /// - an output `O` and what remains from the input: `R`
    /// - an error `E`
    fn apply(&mut self, input: I) -> Result<R, O, E>;
}

/// a pipe is implemented for all closures with the same signature
impl<I, O, E, R, F> Pipe<I, O, E, R> for F
where
    F: FnMut(I) -> Result<R, O, E>,
{
    fn apply(&mut self, input: I) -> Result<R, O, E> { (self)(input) }
}

impl<I, E> Pipe<I, (), E> for () {
    fn apply(&mut self, input: I) -> Result<I, (), E> { Ok((input, ())) }
}
