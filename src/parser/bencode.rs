//! Bencode parsing module
use crate::{
    byte::{ascii_digits, take, TagByteError, TagBytesError},
    tag, AndExt, AndThenExt, EitherExt, Incomplete, MapExt, OptExt, OrExt, Pipe,
    Result as PResult, UnpackExt,
};
use either::Either;
use fatal_error::FatalError;
use std::{
    collections::BTreeMap, fmt::Debug, num::ParseIntError, str::from_utf8_unchecked,
};

/// Bencode parsing error
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// parse int error
    Int(ParseIntError),
    /// Invalid number
    InvalidNumber,
    /// Invalid string size
    InvalidStringSize,
    /// more bytes needed
    Incomplete(Incomplete),
    /// parse max depth reached
    MaxDepth,
    /// invalid dict key
    InvalidKey(Bencode),
    /// dick has a key but no value
    DictNoValue,
    /// tag error
    TagByte(TagByteError),
    /// tag error
    TagBytes(TagBytesError),
}

impl From<ParseIntError> for Error {
    fn from(value: ParseIntError) -> Self { Error::Int(value) }
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

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::Int(x) => write!(f, "Invalid i64: {x}"),
            Error::InvalidNumber => write!(f, "Invalid number"),
            Error::InvalidStringSize => write!(f, "Invalid string size"),
            Error::Incomplete(x) => Debug::fmt(x, f),
            Error::MaxDepth => write!(f, "Max depth reached"),
            Error::InvalidKey(x) => write!(f, "Invalid dict key: {x:?}"),
            Error::DictNoValue => write!(f, "Missing dict value"),
            Error::TagByte(x) => write!(f, "Bencode: {x}",),
            Error::TagBytes(x) => write!(f, "Bencode: {x}",),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Int(x) => Some(x),
            Error::Incomplete(x) => Some(x),
            _ => None,
        }
    }
}

/// Bencode element
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bencode {
    /// Bencode integer
    Integer(i64),
    /// Bencode string
    String(Vec<u8>),
    /// Bencode list
    List(Vec<Bencode>),
    /// Bencode dict
    Dict(BTreeMap<Vec<u8>, Bencode>),
}

fn integer<'a>(x: &'a [u8]) -> PResult<&'a [u8], (i64,), Error> {
    tag(b'i')
        .and_other(tag(b'-').opt().map1(|x: Option<_>| x.is_some()))
        .and(ascii_digits(1..))
        .and_self(tag(b'e'))
        .and_then(|x, y: &'a [u8]| {
            if (x && y.starts_with(b"0")) || y.starts_with(b"00") {
                Err(FatalError::Fatal(Error::InvalidNumber))
            } else {
                format!(
                    "{}{}",
                    if x { "-" } else { "" },
                    //safe because we read the digits just before
                    unsafe { from_utf8_unchecked(y) }
                )
                .parse::<i64>()
                .map(|x| (x,))
                .map_err(|x| FatalError::Fatal(x.into()))
            }
        })
        .apply(x)
}

fn usize<'a>(x: &'a [u8]) -> PResult<&'a [u8], (usize,), Error> {
    ascii_digits(1..)
        .and_then(|nb: &'a [u8]| match nb {
            b"0" => Ok((0,)),
            x if x.starts_with(b"0") => Err(FatalError::Fatal(Error::InvalidStringSize)),
            x => Ok((unsafe { from_utf8_unchecked(x) }
                .parse::<usize>()
                .map_err(|x| FatalError::Fatal(Error::Int(x)))?,)),
        })
        .apply(x)
}

fn string(x: &[u8]) -> PResult<&[u8], (Vec<u8>,), Error> {
    usize
        .and_self(tag(b':'))
        .unpack()
        .ok_and_then(|i, nb| match nb {
            0 => Ok((i, (Vec::new(),))),
            x => take(x).map1(|x: &[u8]| x.to_vec()).apply(i),
        })
        .apply(x)
}

fn single_item(x: &[u8]) -> PResult<&[u8], (Bencode,), Error> {
    integer.map1(Bencode::Integer).or(string.map1(Bencode::String)).apply(x)
}

#[derive(Debug, Default)]
struct DictState {
    data: BTreeMap<Vec<u8>, Bencode>,
    key:  Option<Vec<u8>>,
}

impl DictState {
    fn push_item(&mut self, item: Bencode) -> Result<(), FatalError<Error>> {
        match (self.key.take(), item) {
            (None, Bencode::String(x)) => {
                self.key = Some(x);
                Ok(())
            }
            (Some(k), v @ Bencode::Integer(_)) => {
                self.data.insert(k, v);
                Ok(())
            }
            (Some(k), v @ Bencode::String(_)) => {
                self.data.insert(k, v);
                Ok(())
            }
            (Some(k), v @ Bencode::List(_)) => {
                self.data.insert(k, v);
                Ok(())
            }
            (Some(k), v @ Bencode::Dict(_)) => {
                self.data.insert(k, v);
                Ok(())
            }
            (None, x) => Err(FatalError::Fatal(Error::InvalidKey(x))),
        }
    }

    fn finish(self) -> Result<Bencode, FatalError<Error>> {
        if self.key.is_none() {
            Ok(Bencode::Dict(self.data))
        } else {
            Err(FatalError::Fatal(Error::DictNoValue))
        }
    }
}

enum ListDict {
    List(Vec<Bencode>),
    Dict(DictState),
}

impl ListDict {
    fn push_item(&mut self, item: Bencode) -> Result<(), FatalError<Error>> {
        match self {
            ListDict::List(x) => {
                x.push(item);
                Ok(())
            }
            ListDict::Dict(x) => x.push_item(item),
        }
    }

    fn finish(self) -> Result<Bencode, FatalError<Error>> {
        match self {
            ListDict::List(x) => Ok(Bencode::List(x)),
            ListDict::Dict(x) => x.finish(),
        }
    }
}

fn list_start(i: &[u8]) -> PResult<&[u8], (ListDict,), Error> {
    tag(b'l').map1(|_| ListDict::List(vec![])).apply(i)
}

fn dict_start(i: &[u8]) -> PResult<&[u8], (ListDict,), Error> {
    tag(b'd').map1(|_| ListDict::Dict(DictState::default())).apply(i)
}

fn single_dict_list(i: &[u8]) -> PResult<&[u8], (Either<Bencode, ListDict>,), Error> {
    single_item.either(dict_start.or(list_start)).apply(i)
}

#[inline]
fn bencode_impl(max_depth: usize, i: &[u8]) -> PResult<&[u8], (Bencode,), Error> {
    match single_dict_list.unpack().apply(i)? {
        (i, Either::Left(x)) => Ok((i, (x,))),
        (mut i, Either::Right(x)) => {
            let mut stack = vec![x];
            loop {
                if stack.len() > max_depth {
                    return Err(FatalError::Fatal(Error::MaxDepth));
                }
                let ln = i.len();
                if let (r, Some(_)) = tag(b'e').opt().unpack().apply(i)? {
                    let x = stack.pop().unwrap().finish()?;
                    if let Some(y) = stack.last_mut() {
                        y.push_item(x)?;
                    } else {
                        return Ok((r, (x,)));
                    }
                    i = r
                }
                if let (r, Some(x)) = single_dict_list.opt().unpack().apply(i)? {
                    match x {
                        Either::Left(x) => stack.last_mut().unwrap().push_item(x)?,
                        Either::Right(x) => stack.push(x),
                    }
                    i = r;
                }
                if ln == i.len() {
                    break;
                }
            }
            if stack.len() == 1 {
                Ok((i, (stack.pop().unwrap().finish()?,)))
            } else {
                Err(FatalError::Fatal(Error::Incomplete(Incomplete::Unknown)))
            }
        }
    }
}

/// parse a buffer containing bencode
///
/// if the bencode tree contains too much nested elements, a stackoverflow may occur on debug and deallocation
pub fn bencode(i: &[u8]) -> PResult<&[u8], (Bencode,), Error> {
    bencode_impl(usize::MAX, i)
}

/// parse a buffer containing bencode
///
/// the function stops parsing bencode if more than max_depth nested items are encountered
pub fn bencode_limited(max_depth: usize, i: &[u8]) -> PResult<&[u8], (Bencode,), Error> {
    bencode_impl(max_depth, i)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_integer() {
        let mut p = integer;
        assert_eq!(p.apply(b"i42e"), Ok((&b""[..], (42i64,))));
        assert_eq!(p.apply(b"i-42e"), Ok((&b""[..], (-42i64,))));
        assert_eq!(p.apply(b"i-0e"), Err(FatalError::Fatal(Error::InvalidNumber)));
        assert_eq!(p.apply(b"i0e"), Ok((&b""[..], (0i64,))));
        assert_eq!(p.apply(b"i0004e"), Err(FatalError::Fatal(Error::InvalidNumber)));
        let max = format!("i{}e", i64::MAX);
        let min = format!("i{}e", i64::MIN);
        assert_eq!(p.apply(max.as_bytes()), Ok((&b""[..], (i64::MAX,))));
        assert_eq!(p.apply(min.as_bytes()), Ok((&b""[..], (i64::MIN,))));
        p.apply(b"i0").expect_err("should fail");
    }

    #[test]
    fn test_string() {
        assert_eq!(string.apply(b"4:spam"), Ok((&b""[..], (b"spam".to_vec(),))));
        assert_eq!(string.apply(b"3:cowd"), Ok((&b"d"[..], (b"cow".to_vec(),))));
        assert_eq!(string.apply(b"0:cowd"), Ok((&b"cowd"[..], (b"".to_vec(),))));
        assert_eq!(string.apply(b"0:"), Ok((&b""[..], (b"".to_vec(),))));
    }

    #[test]
    fn test_list() {
        assert_eq!(
            bencode(b"l4:spam4:eggse"),
            Ok((
                &b""[..],
                (Bencode::List(vec![
                    Bencode::String(b"spam".to_vec()),
                    Bencode::String(b"eggs".to_vec())
                ]),)
            ))
        );
        assert_eq!(
            bencode(b"li10ei12ee"),
            Ok((
                &b""[..],
                (Bencode::List(vec![Bencode::Integer(10), Bencode::Integer(12)]),)
            ))
        );
        assert_eq!(
            bencode(b"l4:spami10e3:cowi12ee"),
            Ok((
                &b""[..],
                (Bencode::List(vec![
                    Bencode::String(b"spam".to_vec()),
                    Bencode::Integer(10),
                    Bencode::String(b"cow".to_vec()),
                    Bencode::Integer(12)
                ]),)
            ))
        );
        assert_eq!(
            bencode(b"l4:spami10e3:cowi12ee"),
            Ok((
                &b""[..],
                (Bencode::List(vec![
                    Bencode::String(b"spam".to_vec()),
                    Bencode::Integer(10),
                    Bencode::String(b"cow".to_vec()),
                    Bencode::Integer(12)
                ]),)
            ))
        );
        assert_eq!(bencode(b"le"), Ok((&b""[..], (Bencode::List(vec![]),))));
    }

    #[test]
    fn test_dict() {
        assert_eq!(
            bencode(b"d3:cow3:moo4:spam4:eggse"),
            Ok((
                &b""[..],
                (Bencode::Dict(
                    [
                        (b"cow".to_vec(), Bencode::String(b"moo".to_vec())),
                        (b"spam".to_vec(), Bencode::String(b"eggs".to_vec()))
                    ]
                    .into()
                ),)
            ))
        );
        assert_eq!(
            bencode(b"d4:spaml1:a1:bee"),
            Ok((
                &b""[..],
                (Bencode::Dict(
                    [(
                        b"spam".to_vec(),
                        Bencode::List(
                            [
                                Bencode::String(b"a".to_vec()),
                                Bencode::String(b"b".to_vec())
                            ]
                            .into()
                        )
                    )]
                    .into()
                ),)
            ))
        );

        assert_eq!(
            bencode(b"d9:publisher3:bob17:publisher-webpage15:www.example.com18:publisher.location4:homee"),
            Ok((
                &b""[..],
                (Bencode::Dict(
                    [
                        (b"publisher".to_vec(), Bencode::String(b"bob".to_vec())),
                        (b"publisher-webpage".to_vec(), Bencode::String(b"www.example.com".to_vec())),
                        (b"publisher.location".to_vec(), Bencode::String(b"home".to_vec()))
                    ]
                    .into()
                ),)
            ))
        );

        assert_eq!(bencode(b"de"), Ok((&b""[..], (Bencode::Dict([].into()),))));
    }

    #[test]
    fn test_bencode() {
        let mut p = bencode;
        assert_eq!(p.apply(b"i42e"), Ok((&b""[..], (Bencode::Integer(42i64),))));
        assert_eq!(p.apply(b"i-42e"), Ok((&b""[..], (Bencode::Integer(-42i64),))));
        assert_eq!(p.apply(b"i-0e"), Err(FatalError::Fatal(Error::InvalidNumber)));
        assert_eq!(p.apply(b"i0e"), Ok((&b""[..], (Bencode::Integer(0i64),))));
        assert_eq!(p.apply(b"i0004e"), Err(FatalError::Fatal(Error::InvalidNumber)));
        let max = format!("i{}e", i64::MAX);
        let min = format!("i{}e", i64::MIN);
        assert_eq!(
            bencode(max.as_bytes()),
            Ok((&b""[..], (Bencode::Integer(i64::MAX),)))
        );
        assert_eq!(
            bencode(min.as_bytes()),
            Ok((&b""[..], (Bencode::Integer(i64::MIN),)))
        );
        assert!(p.apply(b"i0").is_err());
    }

    #[test]
    fn test_nested() {
        const NB: usize = 2000;
        let buf = [b"d5:hellol"; NB]
            .into_iter()
            .flatten()
            .chain([b"ee"; NB].into_iter().flatten())
            .copied()
            .collect::<Vec<u8>>();
        bencode(&buf).expect("should be ok");
    }

    #[test]
    fn test_deeply_nested() {
        const NB: usize = 3000;
        let mut buf = Vec::new();
        buf.resize(NB, b'l');
        buf.resize(NB * 2, b'e');
        assert_eq!(bencode_limited(NB - 1, &buf), Err(FatalError::Fatal(Error::MaxDepth)))
    }
}
