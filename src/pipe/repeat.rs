use crate::{Pipe, Result as PResult};
use fatal_error::FatalError;
use std::{
    convert::Infallible,
    marker::PhantomData,
    ops::{
        Bound, Range, RangeBounds, RangeFrom, RangeFull, RangeInclusive, RangeTo,
        RangeToInclusive,
    },
};
use tuplify::Unpack;

/// Invalid repetition
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidRepetition(usize, usize);

impl From<Infallible> for InvalidRepetition {
    fn from(_: Infallible) -> Self { unreachable!() }
}

impl std::fmt::Display for InvalidRepetition {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Invalid repetition: min: {} - max: {}", self.0, self.1)
    }
}

impl std::error::Error for InvalidRepetition {}

/// Represents a range or a fixed number
///
/// the upper limit is optionally defined
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Repetition {
    min: usize,
    max: Option<usize>,
}

impl Repetition {
    /// Creates a new repetition
    ///
    /// `max` is inclusive
    ///
    /// returns an error if `min` > `max`
    pub fn range(min: usize, max: Option<usize>) -> Result<Self, InvalidRepetition> {
        if max.map_or(true, |x| x >= min) {
            Ok(Repetition { min, max })
        } else {
            Err(InvalidRepetition(min, max.unwrap()))
        }
    }

    /// Creates a new repetition with a fixed number
    pub fn exact(n: usize) -> Result<Self, InvalidRepetition> {
        Ok(Repetition { min: n, max: Some(n) })
    }

    /// Return true if `nb` < `min`
    pub fn needs_more(&self, nb: usize) -> bool { nb < self.min }

    /// Return true if `nb` == `max`
    pub fn is_max(&self, nb: usize) -> bool { self.max.map_or(false, |x| nb == x) }

    /// Error handling
    ///
    /// Calls the provided function `f` with `min`, `max`, `nb` if `nb` is outside of the repetition boundaries
    pub fn map_err<E>(
        &self, nb: usize, f: impl FnOnce(usize, Option<usize>, usize) -> E,
    ) -> Result<(), E> {
        if nb >= self.min && self.max.map_or(true, |x| nb <= x) {
            Ok(())
        } else {
            Err(f(self.min, self.max, nb))
        }
    }

    /// Returns the minimum number of repetitions needed after `nb` repetitions
    pub fn min_needed(&self, nb: usize) -> usize { self.min.saturating_sub(nb) }
}

impl TryFrom<usize> for Repetition {
    type Error = InvalidRepetition;

    fn try_from(value: usize) -> Result<Self, Self::Error> { Self::exact(value) }
}

impl From<RangeFrom<usize>> for Repetition {
    fn from(value: RangeFrom<usize>) -> Self {
        Repetition { min: value.start, max: None }
    }
}

impl From<RangeFull> for Repetition {
    fn from(_: RangeFull) -> Self { Repetition { min: 0, max: None } }
}

impl TryFrom<Range<usize>> for Repetition {
    type Error = InvalidRepetition;

    fn try_from(value: Range<usize>) -> Result<Self, Self::Error> {
        Repetition::range(
            value.start,
            match value.end_bound() {
                Bound::Included(x) => Some(*x),
                Bound::Excluded(x) => Some(x.saturating_sub(1)),
                Bound::Unbounded => None,
            },
        )
    }
}

impl TryFrom<RangeInclusive<usize>> for Repetition {
    type Error = InvalidRepetition;

    fn try_from(value: RangeInclusive<usize>) -> Result<Self, Self::Error> {
        Repetition::range(*value.start(), Some(*value.end()))
    }
}

impl TryFrom<RangeTo<usize>> for Repetition {
    type Error = InvalidRepetition;

    fn try_from(value: RangeTo<usize>) -> Result<Self, Self::Error> {
        Repetition::range(0, Some(value.end.saturating_sub(1)))
    }
}

impl TryFrom<RangeToInclusive<usize>> for Repetition {
    type Error = InvalidRepetition;

    fn try_from(value: RangeToInclusive<usize>) -> Result<Self, Self::Error> {
        Repetition::range(0, Some(value.end))
    }
}

/// Combinator that makes repetitions
pub trait RepeatExt<I, O, E> {
    /// Repeats this pipe.
    ///
    /// The repetition can be a fixed number or a range
    fn repeat<R>(self, r: R) -> RepeatPipe<Self, O>
    where
        R: TryInto<Repetition>,
        R::Error: std::error::Error,
        Self: Pipe<I, O, E> + Sized,
    {
        RepeatPipe::new(self, r.try_into().unwrap())
    }
}

impl<I, O, E, P> RepeatExt<I, O, E> for P where P: Pipe<I, O, E> {}

/// [RepeatExt::repeat] implementation
pub struct RepeatPipe<P, O> {
    p: P,
    r: Repetition,
    o: PhantomData<O>,
}

impl<P, O> RepeatPipe<P, O> {
    fn new(p: P, r: Repetition) -> Self { Self { p, r, o: PhantomData } }
}

impl<I, O, E, P> Pipe<I, (Vec<O::Output>,), E> for RepeatPipe<P, O>
where
    I: Clone,
    O: Unpack,
    P: Pipe<I, O, E> + Sized,
{
    fn apply(&mut self, mut input: I) -> PResult<I, (Vec<O::Output>,), E> {
        let mut r = Vec::new();
        for x in 0.. {
            match self.p.apply(input.clone()) {
                Ok((i, o)) => {
                    input = i;
                    r.push(o.unpack());
                }
                Err(e @ FatalError::Error(_)) => {
                    if self.r.needs_more(x) {
                        return Err(e);
                    } else {
                        break;
                    }
                }
                Err(x) => return Err(x),
            }
            if self.r.is_max(x) {
                break;
            }
        }
        Ok((input, (r,)))
    }
}
