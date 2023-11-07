use crate::{Incomplete, Pipe, Repetition};
use fatal_error::FatalError;
use std::error::Error as StdError;

/// Implemented by [TakeAtom::Atom] to have an atom length
pub trait LenBytes {
    /// number of bytes
    fn len_bytes(&self) -> usize;
}

/// Implemented by types usable with [take_while]
pub trait TakeAtom {
    /// a single element
    type Atom: LenBytes;
    /// a container of [TakeAtom::Atom]
    type Container;

    /// Gets the next [TakeAtom::Atom] and it's index in the container
    fn next(&mut self) -> Option<(usize, Self::Atom)>;

    /// returns a tuple containing `(remaining, consumed)`
    ///  where `consumed` contains all of the items returned by [TakeAtom::next]
    fn split_at(self, index: usize) -> (Self::Container, Self::Container);
}

/// Returns the longest input that matches the predicate
///
/// If quantity condition is not attained an error is returned
#[inline]
pub fn take_while<I, E>(
    mut f: impl FnMut(I::Atom) -> bool,
    qty: impl TryInto<Repetition, Error = impl StdError>,
) -> impl Pipe<I, (I::Container,), E, I::Container>
where
    I: TakeAtom,
    Incomplete: Into<E>,
{
    let qty = qty.try_into().unwrap();
    #[inline]
    move |mut input: I| {
        let mut c = 0;
        let mut idx = 0;
        let mut err = None;
        let mut all = false;
        while !qty.is_max(c) {
            if let Some((i, x)) = input.next() {
                let end = i + x.len_bytes();
                if !f(x) {
                    err = Some(Incomplete::Unknown.into());
                    break;
                }
                idx = end;
                c += 1;
            } else {
                all = true;
                break;
            }
        }
        qty.map_err(c, |_, _, _| {
            if all {
                FatalError::Error(Incomplete::Unknown.into())
            } else {
                FatalError::Error(err.unwrap())
            }
        })?;
        let (r, x) = input.split_at(idx);
        Ok((r, (x,)))
    }
}

/// creates a pipe that takes `qty` of [TakeAtom]
///
/// examples see: [sentences][crate::str::sentences], [words][crate::str::words]
pub fn take_atom<A: TakeAtom, E, E2>(
    qty: impl TryInto<Repetition, Error = E>,
) -> Result<impl Pipe<A, (Vec<A::Atom>,), E2, A::Container>, E>
where
    Incomplete: Into<E2>,
{
    let qty = qty.try_into()?;
    Ok(move |mut input: A| {
        let mut r = Vec::new();
        let mut last = 0;
        for x in 0.. {
            match input.next() {
                Some((i, o)) => {
                    last = i + o.len_bytes();
                    r.push(o);
                }
                None => {
                    if qty.needs_more(x) {
                        return Err(FatalError::Error(Incomplete::Unknown.into()));
                    } else {
                        break;
                    }
                }
            }
            if qty.is_max(x) {
                break;
            }
        }
        Ok((input.split_at(last).0, (r,)))
    })
}
