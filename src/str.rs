//! [str] related combinators
use crate::{
    take_atom, take_while, Incomplete, InvalidRepetition, LenBytes, Pipe, Repetition,
    Tag, TakeAtom,
};
use std::{error::Error as StdError, str::CharIndices};
use tuplify::PushBack;
use unicode_segmentation::{
    GraphemeIndices, USentenceBoundIndices, UWordBoundIndices, UnicodeSegmentation,
};

impl LenBytes for char {
    fn len_bytes(&self) -> usize { self.len_utf8() }
}

impl LenBytes for &str {
    fn len_bytes(&self) -> usize { self.len() }
}

/// Splits an [str] in chars
pub struct CharAtom<'a>(&'a str, CharIndices<'a>);

impl<'a> From<&'a str> for CharAtom<'a> {
    fn from(value: &'a str) -> Self { CharAtom(value, value.char_indices()) }
}

impl<'a> TakeAtom for CharAtom<'a> {
    type Atom = char;
    type Container = &'a str;

    fn next(&mut self) -> Option<(usize, Self::Atom)> { self.1.next() }

    fn split_at(self, index: usize) -> (Self::Container, Self::Container) {
        (&self.0[index..], &self.0[..index])
    }
}

#[cfg(feature = "unicode")]
/// Splits an [str] in graphemes see: [UnicodeSegmentation::graphemes]
pub struct GraphemeAtom<'a>(&'a str, GraphemeIndices<'a>);

#[cfg(feature = "unicode")]
impl<'a> From<&'a str> for GraphemeAtom<'a> {
    fn from(value: &'a str) -> Self { GraphemeAtom(value, value.grapheme_indices(true)) }
}

#[cfg(feature = "unicode")]
impl<'a> TakeAtom for GraphemeAtom<'a> {
    type Atom = &'a str;
    type Container = &'a str;

    fn next(&mut self) -> Option<(usize, Self::Atom)> { self.1.next() }

    fn split_at(self, index: usize) -> (Self::Container, Self::Container) {
        (&self.0[index..], &self.0[..index])
    }
}

#[cfg(feature = "unicode")]
/// Splits an [str] in words see: [UnicodeSegmentation::unicode_words]
pub struct WordAtom<'a>(&'a str, UWordBoundIndices<'a>);

#[cfg(feature = "unicode")]
impl<'a> From<&'a str> for WordAtom<'a> {
    fn from(value: &'a str) -> Self { WordAtom(value, value.split_word_bound_indices()) }
}

#[cfg(feature = "unicode")]
impl<'a> TakeAtom for WordAtom<'a> {
    type Atom = &'a str;
    type Container = &'a str;

    fn next(&mut self) -> Option<(usize, Self::Atom)> { self.1.next() }

    fn split_at(self, index: usize) -> (Self::Container, Self::Container) {
        (&self.0[index..], &self.0[..index])
    }
}

#[cfg(feature = "unicode")]
/// Splits an [str] in sentences see: [UnicodeSegmentation::unicode_sentences]
pub struct SentenceAtom<'a>(&'a str, USentenceBoundIndices<'a>);

#[cfg(feature = "unicode")]
impl<'a> From<&'a str> for SentenceAtom<'a> {
    fn from(value: &'a str) -> Self {
        SentenceAtom(value, value.split_sentence_bound_indices())
    }
}

#[cfg(feature = "unicode")]
impl<'a> TakeAtom for SentenceAtom<'a> {
    type Atom = &'a str;
    type Container = &'a str;

    fn next(&mut self) -> Option<(usize, Self::Atom)> { self.1.next() }

    fn split_at(self, index: usize) -> (Self::Container, Self::Container) {
        (&self.0[index..], &self.0[..index])
    }
}

/// Takes the given quantity of ascii whitespaces
pub fn whitespaces<'a, E>(
    qty: impl TryInto<Repetition, Error = impl Into<InvalidRepetition>>,
) -> impl Pipe<&'a str, (&'a str,), E>
where
    Incomplete: Into<E>,
    E: StdError,
{
    let qty = qty.try_into().map_err(Into::into).unwrap();
    move |i: &'a str| {
        take_while(|x: char| x.is_ascii_whitespace(), qty).apply(CharAtom::from(i))
    }
}

/// Takes the given quantity of ascii digits
pub fn digits<'a, E>(
    qty: impl TryInto<Repetition, Error = impl Into<InvalidRepetition>>,
) -> impl Pipe<&'a str, (&'a str,), E>
where
    Incomplete: Into<E>,
    E: StdError,
{
    let qty = qty.try_into().map_err(Into::into).unwrap();
    move |i: &'a str| {
        take_while(|x: char| x.is_ascii_digit(), qty).apply(CharAtom::from(i))
    }
}

/// Takes the given quantity of ascii hexadecimal digits
pub fn hex_digits<'a, E>(
    qty: impl TryInto<Repetition, Error = impl Into<InvalidRepetition>>,
) -> impl Pipe<&'a str, (&'a str,), E>
where
    Incomplete: Into<E>,
    E: StdError,
{
    let qty = qty.try_into().map_err(Into::into).unwrap();
    move |i: &'a str| {
        take_while(|x: char| x.is_ascii_hexdigit(), qty).apply(CharAtom::from(i))
    }
}

/// Takes the given quantity of ascii octal digits
pub fn oct_digits<'a, E>(
    qty: impl TryInto<Repetition, Error = impl Into<InvalidRepetition>>,
) -> impl Pipe<&'a str, (&'a str,), E>
where
    Incomplete: Into<E>,
    E: StdError,
{
    let qty = qty.try_into().map_err(Into::into).unwrap();
    move |i: &'a str| {
        take_while(|x: char| matches!(x, '0'..='7'), qty).apply(CharAtom::from(i))
    }
}

/// Takes the given quantity of ascii binary digits
pub fn bin_digits<'a, E>(
    qty: impl TryInto<Repetition, Error = impl Into<InvalidRepetition>>,
) -> impl Pipe<&'a str, (&'a str,), E>
where
    Incomplete: Into<E>,
    E: StdError,
{
    let qty = qty.try_into().map_err(Into::into).unwrap();
    move |i: &'a str| {
        take_while(|x: char| matches!(x, '0'..='1'), qty).apply(CharAtom::from(i))
    }
}

/// str tag error containing the expected and found string
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TagStrError(pub String, pub String);

impl std::fmt::Display for TagStrError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Tag: expected: '{}' got: '{}'", self.0, self.1)
    }
}

impl std::error::Error for TagStrError {}

impl<'a, 'b, E> Tag<&'a str, E> for &'b str
where
    E: StdError,
    Incomplete: Into<E>,
    TagStrError: Into<E>,
{
    type Output = &'a str;

    fn strip_from(&self, input: &'a str) -> Result<(&'a str, (Self::Output,)), E> {
        if let Some(x) = input.strip_prefix(self) {
            Ok((x, (&input[..self.len()],)))
        } else {
            Err(if self.starts_with(input) {
                Incomplete::Size(self.len() - input.len()).into()
            } else {
                let end = if input.len() < self.len() {
                    input.len()
                } else {
                    input.ceil_char_boundary(self.len())
                };
                TagStrError(self.to_string(), input[..end].to_string()).into()
            })
        }
    }
}

/// char tag error containing the expected and found char
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TagCharError(pub char, pub char);

impl std::fmt::Display for TagCharError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Tag: expected: '{}' got: '{}'", self.0, self.1)
    }
}

impl std::error::Error for TagCharError {}

impl<'a, E> Tag<&'a str, E> for char
where
    E: StdError,
    Incomplete: Into<E>,
    TagCharError: Into<E>,
{
    type Output = char;

    fn strip_from(&self, input: &'a str) -> Result<(&'a str, (Self::Output,)), E> {
        if let Some(x) = input.strip_prefix(*self) {
            Ok((x, (*self,)))
        } else {
            Err(if input.len() < self.len_utf8() {
                Incomplete::Size(self.len_utf8() - input.len()).into()
            } else {
                TagCharError(*self, input.chars().next().unwrap()).into()
            })
        }
    }
}

/// takes `qty` of chars from an input
///
/// ```rust
/// # use pipe_chain::{
/// #   str::chars,
/// #   Incomplete, Pipe,
/// # };
/// assert_eq!(
///     chars::<_, Incomplete>(..5).unwrap().apply("aỹe"),
///     Ok(("", (vec!['a', 'y', '\u{0303}', 'e'],)))
/// );
/// ```
pub fn chars<'a, E, E2>(
    qty: impl TryInto<Repetition, Error = E>,
) -> Result<impl Pipe<&'a str, (Vec<char>,), E2>, E>
where
    Incomplete: Into<E2>,
{
    let qty = qty.try_into()?;
    Ok(move |input| take_atom(qty).unwrap().apply(CharAtom::from(input)))
}

/// takes `qty` of graphemes clusters from an input
///
/// ```rust
/// # use pipe_chain::{
/// #   str::graphemes,
/// #   Incomplete, Pipe,
/// # };
/// assert_eq!(
///     graphemes::<_, Incomplete>(..5).unwrap().apply("aỹe"),
///     Ok(("", (vec!["a", "ỹ", "e"],)))
/// );
/// ```
pub fn graphemes<'a, E, E2>(
    qty: impl TryInto<Repetition, Error = E>,
) -> Result<impl Pipe<&'a str, (Vec<&'a str>,), E2>, E>
where
    Incomplete: Into<E2>,
{
    let qty = qty.try_into()?;
    Ok(move |input| take_atom(qty).unwrap().apply(GraphemeAtom::from(input)))
}

/// takes `qty` of words from an input
///
/// ```rust
/// # use pipe_chain::{
/// #   str::words,
/// #   Incomplete, Pipe,
/// # };
/// assert_eq!(
///     words::<_, Incomplete>(..5)
///         .unwrap()
///         .apply("Pack my box with five dozen liquor jugs."),
///     Ok((" with five dozen liquor jugs.", (vec!["Pack", " ", "my", " ", "box",],)))
/// );
/// ```
pub fn words<'a, E, E2>(
    qty: impl TryInto<Repetition, Error = E>,
) -> Result<impl Pipe<&'a str, (Vec<&'a str>,), E2>, E>
where
    Incomplete: Into<E2>,
{
    let qty = qty.try_into()?;
    Ok(move |input| take_atom(qty).unwrap().apply(WordAtom::from(input)))
}

/// takes `qty` of sentences from an input
/// /// takes `qty` of words from an input
///
/// ```rust
/// # use pipe_chain::{
/// #   str::{sentences, words},
/// #   Incomplete, Pipe,
/// # };
/// assert_eq!(
///     sentences::<_, Incomplete>(..2)
///         .unwrap()
///         .apply("Sentence 1. Sentence 2. Sentence 3. Sentence 4"),
///     Ok(("Sentence 3. Sentence 4", (vec!["Sentence 1. ", "Sentence 2. "],)))
/// );
/// assert_eq!(
///     sentences::<_, Incomplete>(..)
///         .unwrap()
///         .apply("Sentence 1. Sentence 2. Sentence 3. Sentence 4"),
///     Ok(("", (vec!["Sentence 1. ", "Sentence 2. ", "Sentence 3. ", "Sentence 4"],)))
/// );
/// ```
pub fn sentences<'a, E, E2>(
    qty: impl TryInto<Repetition, Error = E>,
) -> Result<impl Pipe<&'a str, (Vec<&'a str>,), E2>, E>
where
    Incomplete: Into<E2>,
{
    let qty = qty.try_into()?;
    Ok(move |input| take_atom(qty).unwrap().apply(SentenceAtom::from(input)))
}

/// Returns the consumed input instead of the pipe result
/// ```rust
/// # use fatal_error::FatalError;
/// # use pipe_chain::{Pipe, AndExt, AndThenExt, tag, str::{consumed, TagStrError}, Incomplete};
/// # #[derive(Debug, PartialEq, Eq)]
/// # enum Error {
/// #     Incomplete(Incomplete),
/// #     Tag(TagStrError)
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
/// # impl From<TagStrError> for Error {
/// #     fn from(value: TagStrError) -> Self { Error::Tag(value) }
/// # }
/// #
/// # impl std::error::Error for Error {}
/// assert_eq!(
///     consumed(tag::<Error, _, _>("foo").and(tag("bar"))).apply("foobarbaz"),
///     Ok(("baz", ("foobar",)))
/// );
/// ```
pub fn consumed<'a, O, E>(
    mut p: impl Pipe<&'a str, O, E>,
) -> impl Pipe<&'a str, (&'a str,), E> {
    move |x: &'a str| {
        let (i, _) = p.apply(x)?;
        Ok((i, (&x[..x.len() - i.len()],)))
    }
}

/// Get the consumed offset in bytes in addition to the output of the given [Pipe]
/// ```rust
/// # use pipe_chain::{
/// #     str::{consumed, with_offset, TagStrError},
/// #     tag, AndExt, Incomplete, Pipe,
/// # };
/// # use fatal_error::FatalError;
/// #
/// # #[derive(Debug, PartialEq, Eq)]
/// # enum Error {
/// #     Incomplete(Incomplete),
/// #     Tag(TagStrError),
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
/// # impl From<TagStrError> for Error {
/// #     fn from(value: TagStrError) -> Self { Error::Tag(value) }
/// # }
/// #
/// # impl std::error::Error for Error {}
/// assert_eq!(
///     with_offset(tag::<Error, _, _>("foo").and(tag("bar"))).apply("foobarbaz"),
///     Ok(("baz", ("foo", "bar", 6)))
/// );
/// ```
pub fn with_offset<'a, O: PushBack<usize>, E>(
    mut p: impl Pipe<&'a str, O, E>,
) -> impl Pipe<&'a str, O::Output, E> {
    move |x: &'a str| {
        let (i, o) = p.apply(x)?;
        Ok((i, (o.push_back(x.len() - i.len()))))
    }
}

#[cfg(test)]
mod test {

    use crate::{str::sentences, Incomplete, Pipe};

    #[test]
    fn test_unicode() {
        assert_eq!(
            sentences::<_, Incomplete>(..)
                .unwrap()
                .apply("Pack my box with five dozen liquor jugs."),
            Ok(("", (vec!["Pack my box with five dozen liquor jugs.",],)))
        );
    }
}
