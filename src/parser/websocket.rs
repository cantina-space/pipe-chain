//! websocket parser
use crate::{
    byte::{be_u16, be_u64, const_take, take},
    AndThenExt, Incomplete, MapExt, Pipe, Result as PResult,
};
use fatal_error::FatalError;
use std::ops::Deref;

/// Websocket frame opcode
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum OpCode {
    /// Continuation frame
    Continuation,
    /// Text frame
    Text,
    /// Binary frame
    Binary,
    /// NonControl1 frame
    NonControl1,
    /// NonControl2 frame
    NonControl2,
    /// NonControl3 frame
    NonControl3,
    /// NonControl4 frame
    NonControl4,
    /// NonControl5 frame
    NonControl5,
    /// Close frame
    Close,
    /// Ping frame
    Ping,
    /// Pong frame
    Pong,
    /// Control1 frame
    Control1,
    /// Control2 frame
    Control2,
    /// Control3 frame
    Control3,
    /// Control4 frame
    Control4,
    /// Control5 frame
    Control5,
    /// Future proof not in the rfc
    Other(u8),
}

/// Unknown opcode
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct InvalidOpCode(u8);

impl OpCode {
    /// validates this opcode
    pub fn validate(self) -> Result<OpCode, InvalidOpCode> {
        match self {
            OpCode::Other(x) => Err(InvalidOpCode(x)),
            x => Ok(x),
        }
    }
}

impl From<u8> for OpCode {
    fn from(x: u8) -> Self {
        match x {
            0 => OpCode::Continuation,
            1 => OpCode::Text,
            2 => OpCode::Binary,
            3 => OpCode::NonControl1,
            4 => OpCode::NonControl2,
            5 => OpCode::NonControl3,
            6 => OpCode::NonControl4,
            7 => OpCode::NonControl5,
            8 => OpCode::Close,
            9 => OpCode::Ping,
            10 => OpCode::Pong,
            11 => OpCode::Control1,
            12 => OpCode::Control2,
            13 => OpCode::Control3,
            14 => OpCode::Control4,
            15 => OpCode::Control5,
            x => OpCode::Other(x),
        }
    }
}

impl From<OpCode> for u8 {
    fn from(x: OpCode) -> Self {
        match x {
            OpCode::Continuation => 0,
            OpCode::Text => 1,
            OpCode::Binary => 2,
            OpCode::NonControl1 => 3,
            OpCode::NonControl2 => 4,
            OpCode::NonControl3 => 5,
            OpCode::NonControl4 => 6,
            OpCode::NonControl5 => 7,
            OpCode::Close => 8,
            OpCode::Ping => 9,
            OpCode::Pong => 10,
            OpCode::Control1 => 11,
            OpCode::Control2 => 12,
            OpCode::Control3 => 13,
            OpCode::Control4 => 14,
            OpCode::Control5 => 15,
            OpCode::Other(x) => x,
        }
    }
}

impl std::ops::Deref for OpCode {
    type Target = u8;

    fn deref(&self) -> &Self::Target {
        match self {
            OpCode::Continuation => &0,
            OpCode::Text => &1,
            OpCode::Binary => &2,
            OpCode::NonControl1 => &3,
            OpCode::NonControl2 => &4,
            OpCode::NonControl3 => &5,
            OpCode::NonControl4 => &6,
            OpCode::NonControl5 => &7,
            OpCode::Close => &8,
            OpCode::Ping => &9,
            OpCode::Pong => &10,
            OpCode::Control1 => &11,
            OpCode::Control2 => &12,
            OpCode::Control3 => &13,
            OpCode::Control4 => &14,
            OpCode::Control5 => &15,
            OpCode::Other(x) => x,
        }
    }
}

/// Packet Size
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Size {
    /// u8 packet size
    U8(u8),
    /// u16 packet size
    U16(u16),
    /// u64 packet size
    U64(u64),
}

impl Size {
    /// First byte of the packet size
    pub fn first_byte(&self) -> u8 {
        match self {
            Size::U8(x) => *x,
            Size::U16(_) => 126,
            Size::U64(_) => 127,
        }
    }

    /// remaining byte of the packet size
    pub fn final_size(self) -> Vec<u8> {
        match self {
            Size::U8(_) => vec![],
            Size::U16(x) => x.to_be_bytes().to_vec(),
            Size::U64(x) => x.to_be_bytes().to_vec(),
        }
    }
}

impl From<Size> for usize {
    fn from(x: Size) -> Self {
        match x {
            Size::U8(ref v) => *v as usize,
            Size::U16(ref v) => *v as usize,
            Size::U64(ref v) => *v as usize,
        }
    }
}

/// Websocket frame
#[derive(Debug, Clone)]
pub struct Frame {
    fin:    bool,
    rsv1:   bool,
    rsv2:   bool,
    rsv3:   bool,
    opcode: OpCode,
    mask:   Option<[u8; 4]>,
    size:   Size,
    data:   Vec<u8>,
}

impl Frame {
    /// apply the mask on frame data
    pub fn mask(mut self) -> Frame {
        if let Some(mask) = &self.mask {
            for (i, v) in self.data.iter_mut().enumerate() {
                *v ^= mask[i % 4];
            }
        }
        self
    }

    /// Transforms this frame into a bytes
    pub fn into_vec(self) -> Vec<u8> {
        let b1 = ((self.fin as u8) << 7)
            | ((self.rsv1 as u8) << 6)
            | ((self.rsv2 as u8) << 5)
            | ((self.rsv3 as u8) << 4)
            | (u8::from(self.opcode) & 0x0F);
        let b2 = ((self.mask.is_some() as u8) << 7) | (self.size.first_byte() & 0x7F);
        let mut r = vec![b1, b2];
        r.extend(self.size.final_size());
        if let Some(ref mask) = self.mask {
            r.extend(mask.iter());
        }
        r.extend(&self.data);
        r
    }
}

impl From<Frame> for Vec<u8> {
    fn from(frame: Frame) -> Self { frame.into_vec() }
}

#[derive(Debug, Clone)]
enum FrameState {
    Masked(Frame),
    UnMasked(Frame),
}

impl From<FrameState> for Frame {
    fn from(x: FrameState) -> Self {
        match x {
            FrameState::Masked(x) => x,
            FrameState::UnMasked(x) => x,
        }
    }
}

impl Deref for FrameState {
    type Target = Frame;

    fn deref(&self) -> &Self::Target {
        match self {
            FrameState::Masked(x) | FrameState::UnMasked(x) => x,
        }
    }
}

impl FrameState {
    fn unmask(self) -> FrameState {
        match self {
            FrameState::Masked(frame) => FrameState::UnMasked(frame.mask()),
            x @ FrameState::UnMasked(_) => x,
        }
    }

    fn mask(self) -> FrameState {
        match self {
            FrameState::UnMasked(frame) => FrameState::Masked(frame.mask()),
            x @ FrameState::Masked(_) => x,
        }
    }

    pub fn into_frame(self) -> Frame {
        match self {
            FrameState::Masked(x) | FrameState::UnMasked(x) => x,
        }
    }
}

///
#[derive(Debug, Clone)]
pub struct MaskedFrame(FrameState);

impl MaskedFrame {
    /// mask this frame
    pub fn mask(self) -> MaskedFrame { MaskedFrame(self.0.mask()) }

    /// unmask this frame
    pub fn unmask(self) -> MaskedFrame { MaskedFrame(self.0.unmask()) }

    /// returns this frame inner type
    pub fn into_frame(self) -> Frame { self.0.into_frame() }
}

impl Deref for MaskedFrame {
    type Target = Frame;

    fn deref(&self) -> &Self::Target { &self.0 }
}

impl From<MaskedFrame> for Frame {
    fn from(x: MaskedFrame) -> Self { x.0.into() }
}

/// Frame has an invalid size
#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub struct InvalidFrameSize(u8);

impl std::fmt::Display for InvalidFrameSize {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "InvalidFrameSize: {}", self.0)
    }
}

impl std::error::Error for InvalidFrameSize {}

/// Error during frame size parsing
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FrameSizeError {
    /// Frame size needs more input bytes
    Incomplete(Incomplete),
    /// Frame size is incorrect
    InvalidSize(InvalidFrameSize),
}

impl From<Incomplete> for FrameSizeError {
    fn from(value: Incomplete) -> Self { FrameSizeError::Incomplete(value) }
}

impl From<InvalidFrameSize> for FrameSizeError {
    fn from(value: InvalidFrameSize) -> Self { FrameSizeError::InvalidSize(value) }
}

impl std::fmt::Display for FrameSizeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FrameSizeError::Incomplete(x) => write!(f, "FrameSizeError: {x}"),
            FrameSizeError::InvalidSize(x) => write!(f, "FrameSizeError: {x}"),
        }
    }
}

impl std::error::Error for FrameSizeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            FrameSizeError::Incomplete(x) => Some(x),
            FrameSizeError::InvalidSize(x) => Some(x),
        }
    }
}

fn parse_frame_size(buf: &[u8], head: u16) -> PResult<&[u8], (Size,), FrameSizeError> {
    match (head as u8) & 0x7F {
        x @ 0..=125 => Ok((buf, (Size::U8(x),))),
        126 => be_u16().map1(Size::U16).apply(buf),
        127 => be_u64().map1(Size::U64).apply(buf),
        x => Err(FatalError::Error(InvalidFrameSize(x).into())),
    }
}

/// returns a websocket parser
pub fn frame<'a>() -> impl Pipe<&'a [u8], (Frame,), FrameSizeError> {
    move |x: &'a [u8]| {
        let (buf, (head,)) = be_u16().apply(x)?;
        let (buf, (size, mask)) = { move |x| parse_frame_size(x, head) }
            .ok_and_then(|i, (o,)| {
                if head & 0x80 == 0x80 {
                    Ok(const_take::<4, _>().map(|x: [u8; 4]| (o, Some(x))).apply(i)?)
                } else {
                    Ok((i, (o, None)))
                }
            })
            .apply(buf)?;
        let (buf, (data,)) = take(size.into()).apply(buf)?;
        Ok((
            buf,
            (Frame {
                fin: (head >> 8) & 0x80 == 0x80,
                rsv1: (head >> 8) & 0x40 == 0x40,
                rsv2: (head >> 8) & 0x20 == 0x20,
                rsv3: (head >> 8) & 0x10 == 0x10,
                opcode: (((head >> 8) as u8) & 0x0F).into(),
                size,
                mask,
                data: data.to_vec(),
            },),
        ))
    }
}

/// returns a parser of masked frames
pub fn masked_frame<'a>() -> impl Pipe<&'a [u8], (MaskedFrame,), FrameSizeError> {
    frame().map1(|x: Frame| MaskedFrame(FrameState::Masked(x)))
}

/// returns a parser of unmasked frames
pub fn unmasked_frame<'a>() -> impl Pipe<&'a [u8], (MaskedFrame,), FrameSizeError> {
    frame().map1(|x| MaskedFrame(FrameState::UnMasked(x)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Pipe, UnpackExt};

    #[test]
    fn rfc_tests() {
        // TODO: complete with: https://datatracker.ietf.org/doc/html/rfc6455#section-5.7
        let (x, (f,)) =
            unmasked_frame().apply(&[0x81, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f]).unwrap();
        assert!(x.is_empty());
        assert_eq!(f.data, b"Hello");
        assert!(f.fin);
        assert!(!f.rsv1);
        assert!(!f.rsv2);
        assert!(!f.rsv3);
        assert_eq!(f.mask, None);
        assert_eq!(f.opcode, OpCode::Text);
        assert_eq!(f.size, Size::U8(5));
        let v: Vec<u8> = f.into_frame().into();
        assert_eq!(&v, &[0x81, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f]);
        let (x, (f,)) = masked_frame()
            .apply(&[0x81, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58])
            .unwrap();
        let f = f.unmask();
        assert!(x.is_empty());
        assert_eq!(f.data, b"Hello");

        let r = unmasked_frame().apply(&[0x01, 0x03, 0x48, 0x65, 0x6c]).unwrap();
        assert_eq!(r.0, b"");
        assert_eq!(r.1 .0.data, b"Hel");
        assert!(!r.1 .0.fin);

        let r = unmasked_frame().apply(&[0x80, 0x02, 0x6c, 0x6f]).unwrap();

        assert_eq!(r.0, b"");
        assert_eq!(r.1 .0.data, b"lo");
        assert!(r.1 .0.fin);

        let r =
            unmasked_frame().apply(&[0x89, 0x05, 0x48, 0x65, 0x6c, 0x6c, 0x6f]).unwrap();

        assert_eq!(r.0, b"");
        assert_eq!(r.1 .0.data, b"Hello");
        assert!(r.1 .0.fin);
        assert_eq!(r.1 .0.opcode, OpCode::Ping);

        let r = masked_frame()
            .map1(MaskedFrame::unmask)
            .unpack()
            .apply(&[0x8a, 0x85, 0x37, 0xfa, 0x21, 0x3d, 0x7f, 0x9f, 0x4d, 0x51, 0x58])
            .unwrap();
        assert_eq!(r.0, b"");
        assert_eq!(r.1 .0.data, b"Hello");
        assert!(r.1 .0.fin);
        assert_eq!(r.1 .0.opcode, OpCode::Pong);

        let mut buf = [0u8; 260];
        buf[0] = 0x82;
        buf[1] = 0x7E;
        buf[2] = 0x01;
        let (r, (f,)) = unmasked_frame().apply(&buf).unwrap();
        assert!(r.is_empty());
        assert_eq!(f.size, Size::U16(256));
        let v: Vec<u8> = f.into_frame().into();
        assert_eq!(&v, &buf);
        let mut buf = [0u8; 65546];
        buf[0] = 0x82;
        buf[1] = 0x7F;
        buf[7] = 0x01;
        let (r, (f,)) = unmasked_frame().apply(&buf).unwrap();
        assert!(r.is_empty());
        assert_eq!(f.size, Size::U64(65536));
        let v: Vec<u8> = f.into_frame().into();
        assert_eq!(&v, &buf);
    }
}
