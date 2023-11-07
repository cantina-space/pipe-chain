//! bytes related combinators
use crate::{
    take_while, Incomplete, InvalidRepetition, LenBytes, MapExt, Pipe, Repetition, Tag,
    TakeAtom,
};
use fatal_error::FatalError;
use std::error::Error as StdError;

impl LenBytes for u8 {
    fn len_bytes(&self) -> usize { 1 }
}

/// splits `&[u8]` in bytes
pub struct ByteAtom<'a>(&'a [u8], usize);

impl<'a> From<&'a [u8]> for ByteAtom<'a> {
    fn from(value: &'a [u8]) -> Self { ByteAtom(value, 0) }
}

impl<'a> TakeAtom for ByteAtom<'a> {
    type Atom = u8;
    type Container = &'a [u8];

    fn next(&mut self) -> Option<(usize, Self::Atom)> {
        if let x @ Some(_) = self.0.get(self.1).map(|x| (self.1, *x)) {
            self.1 += 1;
            x
        } else {
            None
        }
    }

    fn split_at(self, index: usize) -> (Self::Container, Self::Container) {
        (&self.0[index..], &self.0[..index])
    }
}

/// splits `&[u8; N]` in bytes
pub struct ConstByteAtom<'a, const N: usize>(&'a [u8; N], usize);

impl<'a, const N: usize> From<&'a [u8; N]> for ConstByteAtom<'a, N> {
    fn from(value: &'a [u8; N]) -> Self { ConstByteAtom(value, 0) }
}

impl<'a, const N: usize> TakeAtom for ConstByteAtom<'a, N> {
    type Atom = u8;
    type Container = &'a [u8];

    fn next(&mut self) -> Option<(usize, Self::Atom)> {
        if self.1 < N {
            let r = Some((self.1, self.0[self.1]));
            self.1 += 1;
            r
        } else {
            None
        }
    }

    fn split_at(self, index: usize) -> (Self::Container, Self::Container) {
        (&self.0[index..], &self.0[..index])
    }
}

/// creates a pipe that gets a certain quantity of ascii digits
///
/// panics if the quantity is invalid
#[inline]
pub fn ascii_digits<'a, E>(
    qty: impl TryInto<Repetition, Error = impl Into<InvalidRepetition>>,
) -> impl Pipe<&'a [u8], (&'a [u8],), E>
where
    Incomplete: Into<E>,
{
    let qty = qty.try_into().map_err(Into::into).unwrap();
    move |i: &'a [u8]| {
        take_while(|x: u8| x.is_ascii_digit(), qty).apply(ByteAtom::from(i))
    }
}

/// Take `n` bytes from a slice
#[inline]
pub fn take<'a, E>(n: usize) -> impl Pipe<&'a [u8], (&'a [u8],), E>
where
    Incomplete: Into<E>,
{
    #[inline]
    move |x: &'a [u8]| {
        if x.len() >= n {
            Ok((&x[n..], (&x[..n],)))
        } else {
            Err(FatalError::Error(Incomplete::Size(n - x.len()).into()))
        }
    }
}

/// Take `N` bytes from a slice
#[inline]
pub fn const_take<'a, const N: usize, E>() -> impl Pipe<&'a [u8], ([u8; N],), E>
where
    Incomplete: Into<E>,
{
    #[inline]
    move |x: &'a [u8]| {
        if x.len() >= N {
            Ok((
                &x[N..],
                (if let Ok(x) = x[..N].try_into() { x } else { unreachable!() },),
            ))
        } else {
            Err(FatalError::Error(Incomplete::Size(N - x.len()).into()))
        }
    }
}

/// Take a big endian [u8] from a slice
#[inline]
pub fn be_u8<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (u8,), E>
where
    Incomplete: Into<E>,
{
    const_take::<1, E>().map(|x: [u8; 1]| (u8::from_be_bytes(x),))
}

/// Take a big endian [u16] from a slice
#[inline]
pub fn be_u16<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (u16,), E>
where
    Incomplete: Into<E>,
{
    const_take::<2, E>().map(|x: [u8; 2]| (u16::from_be_bytes(x),))
}

/// Take a big endian [u32] from a slice
#[inline]
pub fn be_u32<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (u32,), E>
where
    Incomplete: Into<E>,
{
    const_take::<4, E>().map(|x: [u8; 4]| (u32::from_be_bytes(x),))
}

/// Take a big endian [u64] from a slice
#[inline]
pub fn be_u64<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (u64,), E>
where
    Incomplete: Into<E>,
{
    const_take::<8, E>().map(|x: [u8; 8]| (u64::from_be_bytes(x),))
}

/// Take a little endian [u8] from a slice
#[inline]
pub fn le_u8<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (u8,), E>
where
    Incomplete: Into<E>,
{
    const_take::<1, E>().map(|x: [u8; 1]| (u8::from_le_bytes(x),))
}

/// Take a little endian [u16] from a slice
#[inline]
pub fn le_u16<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (u16,), E>
where
    Incomplete: Into<E>,
{
    const_take::<2, E>().map(|x: [u8; 2]| (u16::from_le_bytes(x),))
}

/// Take a little endian [u32] from a slice
#[inline]
pub fn le_u32<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (u32,), E>
where
    Incomplete: Into<E>,
{
    const_take::<4, E>().map(|x: [u8; 4]| (u32::from_le_bytes(x),))
}

/// Take a little endian [u64] from a slice
#[inline]
pub fn le_u64<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (u64,), E>
where
    Incomplete: Into<E>,
{
    const_take::<8, E>().map(|x: [u8; 8]| (u64::from_le_bytes(x),))
}

/// Take a big endian [i8] from a slice
#[inline]
pub fn be_i8<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (i8,), E>
where
    Incomplete: Into<E>,
{
    const_take::<1, E>().map(|x: [u8; 1]| (i8::from_be_bytes(x),))
}

/// Take a big endian [i16] from a slice
#[inline]
pub fn be_i16<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (i16,), E>
where
    Incomplete: Into<E>,
{
    const_take::<2, E>().map(|x: [u8; 2]| (i16::from_be_bytes(x),))
}

/// Take a big endian [i32] from a slice
#[inline]
pub fn be_i32<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (i32,), E>
where
    Incomplete: Into<E>,
{
    const_take::<4, E>().map(|x: [u8; 4]| (i32::from_be_bytes(x),))
}

/// Take a big endian [i64] from a slice
#[inline]
pub fn be_i64<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (i64,), E>
where
    Incomplete: Into<E>,
{
    const_take::<8, E>().map(|x: [u8; 8]| (i64::from_be_bytes(x),))
}

/// Take a little endian [i8] from a slice
#[inline]
pub fn le_i8<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (i8,), E>
where
    Incomplete: Into<E>,
{
    const_take::<1, E>().map(|x: [u8; 1]| (i8::from_le_bytes(x),))
}

/// Take a little endian [i16] from a slice
#[inline]
pub fn le_i16<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (i16,), E>
where
    Incomplete: Into<E>,
{
    const_take::<2, E>().map(|x: [u8; 2]| (i16::from_le_bytes(x),))
}

/// Take a little endian [i32] from a slice
#[inline]
pub fn le_i32<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (i32,), E>
where
    Incomplete: Into<E>,
{
    const_take::<4, E>().map(|x: [u8; 4]| (i32::from_le_bytes(x),))
}

/// Take a little endian [i64] from a slice
#[inline]
pub fn le_i64<'a, E: StdError + 'static>() -> impl Pipe<&'a [u8], (i64,), E>
where
    Incomplete: Into<E>,
{
    const_take::<8, E>().map(|x: [u8; 8]| (i64::from_le_bytes(x),))
}

/// Tag error contains expected and found bytes
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TagBytesError(pub Vec<u8>, pub Vec<u8>);

impl std::fmt::Display for TagBytesError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "expected: '{:?}' got: '{:?}'", self.0, self.1)
    }
}

impl std::error::Error for TagBytesError {}

impl<'a, 'b, E> Tag<&'a [u8], E> for &'b [u8]
where
    E: StdError,
    TagBytesError: Into<E>,
    Incomplete: Into<E>,
{
    type Output = &'a [u8];

    fn strip_from(&self, input: &'a [u8]) -> Result<(&'a [u8], (Self::Output,)), E> {
        if let Some(x) = input.strip_prefix(*self) {
            Ok((x, (&input[..self.len()],)))
        } else {
            Err(if self.starts_with(input) {
                Incomplete::Size(self.len() - input.len()).into()
            } else {
                let end = if input.len() < self.len() { input.len() } else { self.len() };
                TagBytesError(self.to_vec(), input[..end].to_vec()).into()
            })
        }
    }
}

impl<'a, 'b, E, const N: usize> Tag<&'a [u8], E> for &'b [u8; N]
where
    E: StdError,
    Incomplete: Into<E>,
    TagBytesError: Into<E>,
{
    type Output = &'a [u8];

    fn strip_from(&self, input: &'a [u8]) -> Result<(&'a [u8], (Self::Output,)), E> {
        if let Some(x) = input.strip_prefix(*self) {
            Ok((x, (&input[..self.len()],)))
        } else {
            Err(if self.starts_with(input) {
                Incomplete::Size(N - input.len()).into()
            } else {
                let end = if input.len() < N { input.len() } else { N };
                TagBytesError(self.to_vec(), input[..end].to_vec()).into()
            })
        }
    }
}

/// Tag error contains expected and found bytes
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TagByteError(pub u8, pub u8);

impl std::fmt::Display for TagByteError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Expected: '{}' got: '{}'", self.0, self.1)
    }
}

impl std::error::Error for TagByteError {}

impl<'a, E> Tag<&'a [u8], E> for u8
where
    E: StdError,
    Incomplete: Into<E>,
    TagByteError: Into<E>,
{
    type Output = u8;

    fn strip_from(&self, input: &'a [u8]) -> Result<(&'a [u8], (Self::Output,)), E> {
        if let Some(x) = input.strip_prefix(&[*self]) {
            Ok((x, (*self,)))
        } else {
            Err(if input.is_empty() {
                Incomplete::Size(1).into()
            } else {
                TagByteError(*self, input[0]).into()
            })
        }
    }
}

/// Returns the consumed input instead of the pipe result
/// ```rust
/// # use fatal_error::FatalError;
/// # use pipe_chain::{Pipe, AndExt, AndThenExt, tag, byte::consumed, Incomplete, byte::TagBytesError};
/// # #[derive(Debug, PartialEq, Eq)]
/// # enum Error {
/// #     Incomplete(Incomplete),
/// #     Tag(TagBytesError),
/// # }
/// #
/// # impl std::fmt::Display for Error {
/// #     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
/// #         write!(f, "{self:?}")
/// #     }
/// # }
/// #
/// # impl From<Incomplete> for Error {
/// #     fn from(value: Incomplete) -> Self { Error::Incomplete(value) }
/// # }
/// #
/// # impl From<TagBytesError> for Error {
/// #     fn from(value: TagBytesError) -> Self { Error::Tag(value) }
/// # }
/// #
/// # impl std::error::Error for Error {}
/// assert_eq!(
///     consumed(tag::<Error, _, _>(b"foo").and(tag(b"bar"))).apply(b"foobarbaz"),
///     Ok((&b"baz"[..], (&b"foobar"[..],)))
/// );
/// ```
pub fn consumed<'a, O, E>(
    mut p: impl Pipe<&'a [u8], O, E>,
) -> impl Pipe<&'a [u8], (&'a [u8],), E> {
    move |x: &'a [u8]| {
        let (i, _) = p.apply(x)?;
        Ok((i, (&x[..x.len() - i.len()],)))
    }
}

#[cfg(test)]
mod tests {
    use super::TagByteError;
    use crate::{
        byte::{ascii_digits, take, TagBytesError},
        tag, Incomplete, Pipe,
    };
    use fatal_error::FatalError;

    #[derive(Debug, PartialEq, Eq)]
    enum Error {
        Incomplete(Incomplete),
        TagByte(TagByteError),
        TagBytes(TagBytesError),
    }

    impl std::fmt::Display for Error {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{self:?}")
        }
    }

    impl From<Incomplete> for Error {
        fn from(value: Incomplete) -> Self { Error::Incomplete(value) }
    }

    impl From<TagByteError> for Error {
        fn from(value: TagByteError) -> Self { Error::TagByte(value) }
    }

    impl From<TagBytesError> for Error {
        fn from(value: TagBytesError) -> Self { Error::TagBytes(value) }
    }

    impl std::error::Error for Error {}

    #[test]
    fn test_tag() {
        assert_eq!(
            tag::<Error, _, _>(b"foo").apply(b"fooo"),
            Ok((&b"o"[..], (&b"foo"[..],)))
        );
        assert_eq!(
            tag::<Error, _, _>(b"foo").apply(b"fo"),
            Err(FatalError::Error(Error::Incomplete(Incomplete::Size(1))))
        );
        assert_eq!(
            tag::<Error, _, _>(b"foo").apply(b"faaa"),
            Err(FatalError::Error(
                TagBytesError(b"foo".to_vec(), b"faa".to_vec()).into(),
            ))
        );
    }

    #[test]
    fn test_take() {
        assert_eq!(take::<Incomplete>(1).apply(b"yolo"), Ok((&b"olo"[..], (&b"y"[..],))));
        assert_eq!(
            take::<Incomplete>(8).apply(b"yolo"),
            Err(FatalError::Error(Incomplete::Size(4)))
        );
    }

    #[derive(Debug, PartialEq, Eq)]
    enum AsciiiDigitErr {
        Incomplete(Incomplete),
    }

    impl From<Incomplete> for AsciiiDigitErr {
        fn from(value: Incomplete) -> Self { AsciiiDigitErr::Incomplete(value) }
    }

    #[test]
    fn test_digits() {
        assert_eq!(
            ascii_digits::<AsciiiDigitErr>(..).apply(b"0123"),
            Ok((&b""[..], (&b"0123"[..],)))
        );
        assert_eq!(
            ascii_digits::<AsciiiDigitErr>(..).apply(b""),
            Ok((&b""[..], (&b""[..],)))
        );
        assert_eq!(
            ascii_digits::<AsciiiDigitErr>(0..).apply(b""),
            Ok((&b""[..], (&b""[..],)))
        );
        assert_eq!(
            ascii_digits::<AsciiiDigitErr>(10..).apply(b""),
            Err(FatalError::Error(Incomplete::Unknown.into()))
        );
        assert_eq!(
            ascii_digits::<AsciiiDigitErr>(..=1).apply(b"012345"),
            Ok((&b"12345"[..], (&b"0"[..],)))
        );
        assert_eq!(
            ascii_digits::<AsciiiDigitErr>(..2).apply(b"012345"),
            Ok((&b"12345"[..], (&b"0"[..],)))
        );
        assert_eq!(
            ascii_digits::<AsciiiDigitErr>(2..3).apply(b"012345"),
            Ok((&b"2345"[..], (&b"01"[..],)))
        );
        assert_eq!(
            ascii_digits::<AsciiiDigitErr>(2..=2).apply(b"012345"),
            Ok((&b"2345"[..], (&b"01"[..],)))
        );
        assert_eq!(
            ascii_digits::<AsciiiDigitErr>(2..=3).apply(b"012345"),
            Ok((&b"345"[..], (&b"012"[..],)))
        );
        assert_eq!(
            ascii_digits::<AsciiiDigitErr>(2..=6).apply(b"012345abc"),
            Ok((&b"abc"[..], (&b"012345"[..],)))
        );
        assert_eq!(
            ascii_digits::<AsciiiDigitErr>(7..).apply(b"012345abc"),
            Err(FatalError::Error(Incomplete::Unknown.into()))
        );
    }

    #[test]
    #[should_panic(
        expected = "called `Result::unwrap()` on an `Err` value: InvalidRepetition(2, 1)"
    )]
    fn test_digits_invalid2() { ascii_digits::<AsciiiDigitErr>(2..2); }
}
