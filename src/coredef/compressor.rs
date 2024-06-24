use super::error::Result;
use snap::raw::{Decoder, Encoder};

pub trait Compressor {
    /// Returns the id of the compressor
    fn id(&self) -> u8;

    fn encode(&self, data: Vec<u8>) -> Result<Vec<u8>>;

    fn decode(&self, data: Vec<u8>) -> Result<Vec<u8>>;
}

#[derive(Clone, Copy, Default)]
pub struct NoneCompressor;

impl Compressor for NoneCompressor {
    fn id(&self) -> u8 {
        0
    }

    fn encode(&self, data: Vec<u8>) -> Result<Vec<u8>> {
        Ok(data)
    }

    fn decode(&self, data: Vec<u8>) -> Result<Vec<u8>> {
        Ok(data)
    }
}

#[derive(Clone, Copy, Default)]
pub struct SnappyCompressor;

impl Compressor for SnappyCompressor {
    fn id(&self) -> u8 {
        1
    }

    fn encode(&self, data: Vec<u8>) -> Result<Vec<u8>> {
        Ok(Encoder::new().compress_vec(&data)?)
    }

    fn decode(&self, data: Vec<u8>) -> Result<Vec<u8>> {
        Ok(Decoder::new().decompress_vec(&data)?)
    }
}
