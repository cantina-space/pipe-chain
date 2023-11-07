//! Input consumers

use crate::{Incomplete, Pipe};
use fatal_error::FatalError;
use std::error::Error as StdError;

/// Helper trait to recognize a tag
pub trait Tag<T, E> {
    /// Extracted tag
    type Output;

    /// remove self from the begining of `input`
    fn strip_from(&self, input: T) -> Result<(T, (Self::Output,)), E>;
}

/// recognize the given tag at the begining of input
/// 
/// 
pub fn tag<E, I, T: Tag<I, E>>(tag: T) -> impl Pipe<I, (T::Output,), E>
where
    E: StdError,
    Incomplete: Into<E>,
{
    move |i: I| tag.strip_from(i).map_err(FatalError::Error)
}
