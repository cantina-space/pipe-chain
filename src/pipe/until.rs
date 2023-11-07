use crate::{Pipe, Repetition, Result};
use std::marker::PhantomData;
use tuplify::{Extend, HList, Unpack};

/// Until combinator
pub trait UntilExt<I, O, E> {
    /// Applies a [Pipe] until the 2nd succeeds
    fn until<O2, P>(self, p: P) -> Until<Self, P, O, O2>
    where
        I: Clone,
        O: Unpack,
        O2: HList,
        (Vec<O::Output>,): Extend<O2>,
        Self: Sized,
        P: Pipe<I, O2, E>,
    {
        Until::new(self, p)
    }

    /// Applies `self` until `p` succeeds, `self` is applied 0 or more times
    fn no_more_until<O2, P>(self, p: P) -> NoMoreUntil<Self, P, O, O2>
    where
        I: Clone,
        O: Unpack,
        O2: HList,
        (Vec<O::Output>,): Extend<O2>,
        Self: Sized,
        P: Pipe<I, O2, E>,
    {
        NoMoreUntil::new(self, p)
    }

    /// repeats `self` with the given repetition then applies `p`
    fn repeat_until<O2, R, P>(self, r: R, p: P) -> RepeatUntil<Self, P, O, O2>
    where
        I: Clone,
        O: Unpack,
        O2: HList,
        R: TryInto<Repetition>,
        R::Error: std::error::Error,
        (Vec<O::Output>,): Extend<O2>,
        Self: Sized,
        P: Pipe<I, O2, E>,
    {
        RepeatUntil::new(self, p, r.try_into().unwrap())
    }
}

impl<I, O, E, P: Pipe<I, O, E>> UntilExt<I, O, E> for P {}

/// [UntilExt::until] implementation
pub struct Until<P1, P2, O, O2>(P1, P2, PhantomData<O>, PhantomData<O2>);

impl<P1, P2, O, O2> Until<P1, P2, O, O2> {
    fn new(p1: P1, p2: P2) -> Self { Self(p1, p2, PhantomData, PhantomData) }
}

impl<I, O, O2, E, P1, P2> Pipe<I, <(Vec<O::Output>,) as Extend<O2>>::Output, E>
    for Until<P1, P2, O, O2>
where
    I: Clone,
    O: Unpack,
    O2: HList,
    (Vec<O::Output>,): Extend<O2>,
    P1: Pipe<I, O, E>,
    P2: Pipe<I, O2, E>,
{
    fn apply(
        &mut self, mut input: I,
    ) -> Result<I, <(Vec<O::Output>,) as Extend<O2>>::Output, E> {
        let mut r = vec![];
        loop {
            match self.1.apply(input.clone()) {
                Ok((i, x)) => return Ok((i, (r,).extend(x))),
                Err(_) => match self.0.apply(input) {
                    Ok((i, x)) => {
                        input = i;
                        r.push(x.unpack());
                    }
                    Err(x) => return Err(x),
                },
            }
        }
    }
}

/// [UntilExt::no_more_until] implementation
pub struct NoMoreUntil<P1, P2, O, O2>(P1, P2, PhantomData<O>, PhantomData<O2>);

impl<P1, P2, O, O2> NoMoreUntil<P1, P2, O, O2> {
    fn new(p1: P1, p2: P2) -> Self { Self(p1, p2, PhantomData, PhantomData) }
}

impl<I, O, O2, E, P1, P2> Pipe<I, <(Vec<O::Output>,) as Extend<O2>>::Output, E>
    for NoMoreUntil<P1, P2, O, O2>
where
    I: Clone,
    O: Unpack,
    O2: HList,
    (Vec<O::Output>,): Extend<O2>,
    P1: Pipe<I, O, E>,
    P2: Pipe<I, O2, E>,
{
    fn apply(
        &mut self, mut input: I,
    ) -> Result<I, <(Vec<O::Output>,) as Extend<O2>>::Output, E> {
        let mut r = vec![];
        loop {
            match self.0.apply(input.clone()) {
                Ok((i, x)) => {
                    input = i;
                    r.push(x.unpack());
                }
                Err(_) => match self.1.apply(input) {
                    Ok((i, x)) => return Ok((i, (r,).extend(x))),
                    Err(x) => return Err(x),
                },
            }
        }
    }
}

/// [UntilExt::repeat_until] implementation
pub struct RepeatUntil<P1, P2, O, O2>(
    P1,
    P2,
    Repetition,
    PhantomData<O>,
    PhantomData<O2>,
);

impl<P1, P2, O, O2> RepeatUntil<P1, P2, O, O2> {
    fn new(p1: P1, p2: P2, r: Repetition) -> Self {
        Self(p1, p2, r, PhantomData, PhantomData)
    }
}

impl<I, O, O2, E, P1, P2> Pipe<I, <(Vec<O::Output>,) as Extend<O2>>::Output, E>
    for RepeatUntil<P1, P2, O, O2>
where
    I: Clone,
    O: Unpack,
    O2: HList,
    (Vec<O::Output>,): Extend<O2>,
    P1: Pipe<I, O, E>,
    P2: Pipe<I, O2, E>,
{
    fn apply(
        &mut self, mut input: I,
    ) -> Result<I, <(Vec<O::Output>,) as Extend<O2>>::Output, E> {
        let mut r = vec![];
        let mut nb = 0;
        loop {
            if self.2.is_max(nb) {
                let (i, x) = self.1.apply(input)?;
                return Ok((i, (r,).extend(x)));
            }
            if self.2.needs_more(nb) {
                let (i, x) = self.0.apply(input)?;
                input = i;
                r.push(x.unpack());
            } else {
                match self.1.apply(input.clone()) {
                    Ok((i, x)) => {
                        return Ok((i, (r,).extend(x)));
                    }
                    Err(_) => {
                        let (i, x) = self.0.apply(input)?;
                        input = i;
                        r.push(x.unpack());
                    }
                }
            }
            nb += 1;
        }
    }
}
