//! git pktline parser
use crate::{
    byte::{take, TagByteError, TagBytesError},
    tag, Incomplete, MapExt, Pipe, Result,
};
use fatal_error::FatalError;
use std::str::from_utf8_unchecked;

/// PktLine parsing error
#[derive(Debug)]
pub enum PktLineError {
    /// more bytes needed
    Incomplete(Incomplete),
    /// invalid line size
    InvalidSize,
    /// invalid tag
    TagByte(TagByteError),
    /// invalid tag
    TagBytes(TagBytesError),
}

impl From<Incomplete> for PktLineError {
    fn from(value: Incomplete) -> Self { PktLineError::Incomplete(value) }
}

impl From<TagByteError> for PktLineError {
    fn from(value: TagByteError) -> Self { PktLineError::TagByte(value) }
}

impl From<TagBytesError> for PktLineError {
    fn from(value: TagBytesError) -> Self { PktLineError::TagBytes(value) }
}

impl std::fmt::Display for PktLineError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PktLineError::Incomplete(x) => write!(f, "{x}"),
            PktLineError::InvalidSize => write!(f, "invalid size"),
            PktLineError::TagByte(x) => write!(f, "PktLine Error: {x}"),
            PktLineError::TagBytes(x) => write!(f, "PktLine Error: {x}"),
        }
    }
}

impl std::error::Error for PktLineError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            PktLineError::Incomplete(x) => Some(x),
            PktLineError::TagByte(x) => Some(x),
            PktLineError::TagBytes(x) => Some(x),
            _ => None,
        }
    }
}

/// PktLike packet
#[derive(Debug, PartialEq, Eq)]
pub enum PktLine {
    /// flush packed
    Flush,
    /// delim packet
    Delim,
    /// end packet
    End,
    /// data packet
    Data(Vec<u8>),
}

impl PktLine {
    /// creates a new string representing this packet
    pub fn as_string(&self) -> String {
        match self {
            PktLine::Flush => "0000".to_string(),
            PktLine::Delim => "0001".to_string(),
            PktLine::End => "0002".to_string(),
            PktLine::Data(x) => String::from_utf8_lossy(x).to_string(),
        }
    }

    /// creates a new byte array representing this packet
    pub fn into_bytes(self) -> Vec<u8> {
        match self {
            PktLine::Flush => b"0000".to_vec(),
            PktLine::Delim => b"0001".to_vec(),
            PktLine::End => b"0002".to_vec(),
            PktLine::Data(x) => {
                format!("{:04x}", x.len() + 4).into_bytes().into_iter().chain(x).collect()
            }
        }
    }
}

/// Extracts a [PktLine] from bytes and returns it with the remaining bytes in case of failure an error is returned.
pub fn pkt_line<'a>(data: &'a [u8]) -> Result<&'a [u8], (PktLine,), PktLineError> {
    if data.len() < 4 {
        return Err(FatalError::Error(Incomplete::Size(4 - data.len()).into()));
    }
    let (size, data) = data.split_at(4);
    let size = match (size[0], size[1], size[2], size[3]) {
        (
            b'0'..=b'9' | b'a'..=b'f',
            b'0'..=b'9' | b'a'..=b'f',
            b'0'..=b'9' | b'a'..=b'f',
            b'0'..=b'9' | b'a'..=b'f',
        ) => Ok(unsafe {
            u16::from_str_radix(from_utf8_unchecked(size), 16).unwrap_unchecked()
        }),
        _ => Err(FatalError::Fatal(PktLineError::InvalidSize)),
    }?;
    match size {
        0 => Ok((data, (PktLine::Flush,))),
        1 => Ok((data, (PktLine::Delim,))),
        2 => Ok((data, (PktLine::End,))),
        x @ 5..=65520 => take((x - 4) as usize)
            .map1(|x: &'a [u8]| PktLine::Data(x.to_vec()))
            .apply(data),
        _ => Err(FatalError::Fatal(PktLineError::InvalidSize)),
    }
}

/// Extracts [PktLine::Flush] from bytes
pub fn pkt_flush(data: &'_ [u8]) -> Result<&'_ [u8], (PktLine,), PktLineError> {
    tag(b"0000").map1(|_| PktLine::Flush).apply(data)
}

/// Extracts [PktLine::Delim] from bytes
pub fn pkt_delim(data: &'_ [u8]) -> Result<&'_ [u8], (PktLine,), PktLineError> {
    tag(b"0001").map1(|_| PktLine::Delim).apply(data)
}

/// Extracts [PktLine::End] from bytes
pub fn pkt_end(data: &'_ [u8]) -> Result<&'_ [u8], (PktLine,), PktLineError> {
    tag(b"0002").map1(|_| PktLine::End).apply(data)
}
