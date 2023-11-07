//! Predefined parsers
#[cfg(feature = "bencode")]
pub mod bencode;
#[cfg(feature = "pktline")]
pub mod pktline;
#[cfg(feature = "websocket")]
pub mod websocket;
