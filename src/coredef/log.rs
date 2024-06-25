//! Log: consists of blocks.
//! Block: consists of records and an optional padding.
//! Record: [checksum (u32), length (u16), type (u8), data: [u8]]
//!
//! Checksum: crc32 sum of type and data
//! Type: Full, First, Middle, Last. Used when a record is split into multiple blocks.
use super::error::{err, Result, StatusCode};
use crc::Crc;
use integer_encoding::{FixedInt, FixedIntWriter};
use std::io::{self, Read, Write};

const BLOCK_SIZE: usize = 32 * 1024; // 32 KiB
const HEADER_SIZE: usize = 4 + 2 + 1; // checksum (u32), length (u16), type (u8)
const PADDING: [u8; HEADER_SIZE] = [0; HEADER_SIZE];
const CRC: Crc<u32> = Crc::<u32>::new(&crc::CRC_32_CKSUM);

pub struct Logger(pub Box<dyn Write>);

pub fn stderr() -> Logger {
    Logger(Box::new(io::stderr()))
}

#[macro_export]
macro_rules! log {
    ($l:expr) => ($l.as_ref().map(|l| l.borrow_mut().0.write("\n".as_bytes()).is_ok()));
    ($l:expr, $fmt:expr) => (
        $l.as_ref().map(|l| l.borrow_mut().0.write(concat!($fmt, "\n").as_bytes()).is_ok()));
    ($l:expr, $fmt:expr, $($arg:tt)*) => (
        $l.as_ref().map(
            |l| l.borrow_mut().0.write_fmt(format_args!(concat!($fmt, "\n"), $($arg)*)).is_ok()));
}

#[derive(Clone, Copy)]
pub enum RecordType {
    Full = 1,
    First = 2,
    Middle = 3,
    Last = 4,
}

pub struct LogWriter<W: Write> {
    writer: W,
    current_block_offset: usize,
}

impl<W: Write> LogWriter<W> {
    pub fn new(writer: W) -> Self {
        Self {
            writer,
            current_block_offset: 0,
        }
    }

    pub fn new_with_offset(writer: W, offset: usize) -> Self {
        Self {
            writer,
            current_block_offset: offset % BLOCK_SIZE,
        }
    }

    pub fn add_record(&mut self, mut record: &[u8]) -> Result<()> {
        let mut is_first = true;
        while !record.is_empty() {
            let remaining = BLOCK_SIZE - self.current_block_offset;
            if remaining < HEADER_SIZE {
                self.writer.write_all(&PADDING[..remaining])?;
                self.current_block_offset = 0;
            }

            let length = BLOCK_SIZE - self.current_block_offset - HEADER_SIZE;
            let length = length.min(record.len());

            let recordtype = if is_first && length == record.len() {
                RecordType::Full
            } else if is_first {
                RecordType::First
            } else if length == record.len() {
                RecordType::Last
            } else {
                RecordType::Middle
            };

            let mut digest = CRC.digest();
            digest.update(&[recordtype as u8]);
            digest.update(&record[..length]);
            let checksum = mask_crc(digest.finalize());

            self.writer.write_fixedint(checksum)?;
            self.writer.write_fixedint(length as u16)?;
            self.writer.write_fixedint(recordtype as u8)?;
            self.writer.write_all(&record[..length])?;
            self.current_block_offset += HEADER_SIZE + length;

            record = &record[length..];
            is_first = false;
        }
        Ok(())
    }

    pub fn flush(&mut self) -> Result<()> {
        self.writer.flush()?;
        Ok(())
    }
}

pub struct LogReader<R: Read> {
    reader: R,
    current_block_offset: usize,
    scratch: [u8; HEADER_SIZE],
    checksum: bool,
}

impl<R: Read> LogReader<R> {
    pub fn new(reader: R, checksum: bool) -> Self {
        Self {
            reader,
            current_block_offset: 0,
            scratch: [0; HEADER_SIZE],
            checksum,
        }
    }

    /// EOF is reached when returning false.
    pub fn read(&mut self, dst: &mut Vec<u8>) -> Result<bool> {
        let mut dst_offset: usize = 0;
        dst.clear();

        loop {
            let remaining = BLOCK_SIZE - self.current_block_offset;
            if remaining < HEADER_SIZE {
                self.reader.read_exact(&mut self.scratch[..remaining])?;
                self.current_block_offset = 0;
            }

            match self.reader.read(&mut self.scratch)? {
                0 => return Ok(false),
                HEADER_SIZE => (),
                _ => {
                    return err(
                        StatusCode::Corruption,
                        "log reader: read less than header size",
                    )
                }
            }

            self.current_block_offset += HEADER_SIZE;

            let checksum = u32::decode_fixed(&self.scratch[..4]).unwrap();
            let length = u16::decode_fixed(&self.scratch[4..6]).unwrap() as usize;
            let recordtype = self.scratch[6];

            dst.resize(dst_offset + length, 0);
            let _ = self.reader.read(&mut dst[dst_offset..])?;
            self.current_block_offset += length;

            if self.checksum {
                let mut digest = CRC.digest();
                digest.update(&[recordtype]);
                digest.update(&dst[dst_offset..]);
                if unmask_crc(checksum) != digest.finalize() {
                    return err(StatusCode::Corruption, "log reader: checksum mismatch");
                }
            }

            dst_offset += length;

            if recordtype == RecordType::Full as u8 || recordtype == RecordType::Last as u8 {
                return Ok(true);
            }
        }
    }
}

const MASK_DELTA: u32 = 0xa282ead8;

pub fn mask_crc(c: u32) -> u32 {
    (c.wrapping_shr(15) | c.wrapping_shl(17)).wrapping_add(MASK_DELTA)
}

pub fn unmask_crc(c: u32) -> u32 {
    let c = c.wrapping_sub(MASK_DELTA);
    c.wrapping_shr(17) | c.wrapping_shl(15)
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_leveldb_rs {
        use super::*;

        #[test]
        fn test_crc_mask_crc() {
            let crc = CRC.checksum(b"hello world");
            assert_eq!(crc, unmask_crc(mask_crc(crc)));
            assert!(crc != mask_crc(crc));
        }

        #[test]
        fn test_crc_sanity() {
            assert_eq!(0xFFFFFFFF, CRC.checksum(&[0 as u8; 32]));
            assert_eq!(0x9A809998, CRC.checksum(&[0xff as u8; 32]));
        }

        #[test]
        fn test_writer() {
            let data = &[
                "hello world. My first log entry.",
                "and my second",
                "and my third",
            ];
            let mut lw = LogWriter::new(Vec::new());
            let total_len = data.iter().fold(0, |l, d| l + d.len());

            for d in data {
                let _ = lw.add_record(d.as_bytes());
            }

            assert_eq!(lw.current_block_offset, total_len + 3 * super::HEADER_SIZE);
        }

        #[test]
        fn test_writer_append() {
            let data = &[
                "hello world. My first log entry.",
                "and my second",
                "and my third",
            ];

            let mut dst = Vec::new();
            dst.resize(1024, 0 as u8);

            {
                let mut lw = LogWriter::new(std::io::Cursor::new(dst.as_mut_slice()));
                for d in data {
                    let _ = lw.add_record(d.as_bytes());
                }
            }

            let old = dst.clone();

            // Ensure that new_with_off positions the writer correctly. Some ugly mucking about with
            // cursors and stuff is required.
            {
                let offset = data[0].len() + super::HEADER_SIZE;
                let mut lw = LogWriter::new_with_offset(
                    std::io::Cursor::new(&mut dst.as_mut_slice()[offset..]),
                    offset,
                );
                for d in &data[1..] {
                    let _ = lw.add_record(d.as_bytes());
                }
            }
            assert_eq!(old, dst);
        }
    }

    mod tests_gpt_4o_1 {
        #[cfg(test)]
        use super::*;
        use std::io::Cursor;

        const TEST_DATA: &[u8] = b"Hello, world! This is a test data for LogWriter.";

        #[test]
        fn test_mask_unmask_crc() {
            let crc_val: u32 = 0x12345678;
            let masked_crc = mask_crc(crc_val);
            let unmasked_crc = unmask_crc(masked_crc);
            assert_eq!(crc_val, unmasked_crc);
        }

        #[test]
        fn test_log_writer_single_record() {
            let mut buffer = Vec::new();
            {
                let mut log_writer = LogWriter::new(&mut buffer);
                log_writer.add_record(TEST_DATA).unwrap();
                log_writer.flush().unwrap();
            }

            // Ensure the buffer is not empty
            assert!(!buffer.is_empty());
        }

        #[test]
        fn test_log_writer_multiple_records() {
            let mut buffer = Vec::new();
            {
                let mut log_writer = LogWriter::new(&mut buffer);
                log_writer.add_record(&TEST_DATA[..10]).unwrap();
                log_writer.add_record(&TEST_DATA[10..]).unwrap();
                log_writer.flush().unwrap();
            }

            // Ensure the buffer is not empty
            assert!(!buffer.is_empty());
        }

        #[test]
        fn test_log_writer_with_block_padding() {
            let mut buffer = Vec::new();
            {
                let mut log_writer = LogWriter::new_with_offset(&mut buffer, BLOCK_SIZE - 1);
                log_writer.add_record(TEST_DATA).unwrap();
                log_writer.flush().unwrap();
            }

            // Ensure the buffer is not empty
            assert!(!buffer.is_empty());
        }

        #[test]
        fn test_log_reader_single_record() {
            let mut buffer = Vec::new();
            {
                let mut log_writer = LogWriter::new(&mut buffer);
                log_writer.add_record(TEST_DATA).unwrap();
                log_writer.flush().unwrap();
            }

            let mut reader = LogReader::new(Cursor::new(buffer), true);
            let mut result = Vec::new();
            assert!(reader.read(&mut result).unwrap());
            assert_eq!(&result, TEST_DATA);
        }

        #[test]
        fn test_log_reader_multiple_records() {
            let mut buffer = Vec::new();
            {
                let mut log_writer = LogWriter::new(&mut buffer);
                log_writer.add_record(&TEST_DATA[..10]).unwrap();
                log_writer.add_record(&TEST_DATA[10..]).unwrap();
                log_writer.flush().unwrap();
            }

            let mut reader = LogReader::new(Cursor::new(buffer), true);
            let mut result = Vec::new();
            let mut buffer = Vec::new();
            while reader.read(&mut buffer).unwrap() {
                result.extend_from_slice(&buffer);
            }

            assert_eq!(&result, TEST_DATA);
        }

        #[test]
        fn test_log_reader_with_block_padding() {
            let mut buffer = Vec::new();
            {
                let mut log_writer = LogWriter::new(&mut buffer);
                log_writer.add_record(TEST_DATA).unwrap();
                log_writer.flush().unwrap();
            }

            let mut reader = LogReader::new(Cursor::new(buffer), true);
            let mut result = Vec::new();
            assert!(reader.read(&mut result).is_ok());
            assert_eq!(&result, TEST_DATA);
        }

        #[test]
        fn test_log_reader_corrupted_data() {
            let mut buffer = Vec::new();
            {
                let mut log_writer = LogWriter::new(&mut buffer);
                log_writer.add_record(TEST_DATA).unwrap();
                log_writer.flush().unwrap();
            }

            // Corrupt the buffer by modifying a byte
            buffer[10] ^= 0xFF;

            let mut reader = LogReader::new(Cursor::new(buffer), true);
            let mut result = Vec::new();
            let read_result = reader.read(&mut result);
            assert!(read_result.is_err());
        }
    }

    mod tests_gpt_4o_2 {
        use super::*;
        use std::io::Cursor;

        #[test]
        fn test_mask_crc() {
            let crc = 123456789;
            let masked = mask_crc(crc);
            let unmasked = unmask_crc(masked);
            assert_eq!(crc, unmasked, "CRC masking/unmasking failed");
        }

        #[test]
        fn test_unmask_crc() {
            let crc = 987654321;
            let masked = mask_crc(crc);
            let unmasked = unmask_crc(masked);
            assert_eq!(crc, unmasked, "CRC masking/unmasking failed");
        }

        #[test]
        fn test_add_and_read_full_record() {
            let mut buf = Cursor::new(Vec::new());
            let mut writer = LogWriter::new(&mut buf);
            let record = b"Hello, world!";
            writer.add_record(record).unwrap();
            writer.flush().unwrap();

            buf.set_position(0);
            let mut reader = LogReader::new(&mut buf, true);
            let mut dst = Vec::new();
            assert!(reader.read(&mut dst).unwrap());
            assert_eq!(dst, record);
        }

        #[test]
        fn test_add_and_read_multiple_records() {
            let mut buf = Cursor::new(Vec::new());
            let mut writer = LogWriter::new(&mut buf);
            let record1 = b"Hello, world!";
            let record2 = b"Goodbye, world!";
            writer.add_record(record1).unwrap();
            writer.add_record(record2).unwrap();
            writer.flush().unwrap();

            buf.set_position(0);
            let mut reader = LogReader::new(&mut buf, true);
            let mut dst = Vec::new();
            assert!(reader.read(&mut dst).unwrap());
            assert_eq!(dst, record1);
            assert!(reader.read(&mut dst).unwrap());
            assert_eq!(dst, record2);
        }

        #[test]
        fn test_add_and_read_split_record() {
            let mut buf = Cursor::new(Vec::new());
            let mut writer = LogWriter::new_with_offset(&mut buf, BLOCK_SIZE - HEADER_SIZE - 4);
            let record = b"Hello, world! This is a long record that will be split across blocks.";
            writer.add_record(record).unwrap();
            writer.flush().unwrap();

            buf.set_position(0);
            let mut reader = LogReader::new(&mut buf, true);
            let mut dst = Vec::new();
            assert!(reader.read(&mut dst).unwrap());
            assert_eq!(dst, record);
        }

        #[test]
        fn test_checksum_mismatch() {
            let mut buf = Cursor::new(Vec::new());
            let mut writer = LogWriter::new(&mut buf);
            let record = b"Hello, world!";
            writer.add_record(record).unwrap();
            writer.flush().unwrap();

            let mut data = buf.into_inner();
            data[0] = !data[0]; // Invalidate the checksum

            let mut buf = Cursor::new(data);
            let mut reader = LogReader::new(&mut buf, true);
            let mut dst = Vec::new();
            assert!(
                reader.read(&mut dst).is_err(),
                "Expected checksum mismatch error"
            );
        }

        // #[test]
        // fn test_log_writer_padding() {
        //     let mut buf = Cursor::new(Vec::new());
        //     let mut writer = LogWriter::new_with_offset(&mut buf, BLOCK_SIZE - HEADER_SIZE + 1);
        //     let record = b"Test padding record.";
        //     writer.add_record(record).unwrap();
        //     writer.flush().unwrap();

        //     buf.set_position(BLOCK_SIZE as u64);
        //     let mut padding = vec![0; HEADER_SIZE - 1];
        //     buf.read_exact(&mut padding).unwrap();
        //     assert_eq!(&padding, &PADDING[1..]);
        // }

        #[test]
        fn test_log_reader_eof() {
            let mut buf = Cursor::new(Vec::new());
            let mut writer = LogWriter::new(&mut buf);
            let record = b"EOF test record.";
            writer.add_record(record).unwrap();
            writer.flush().unwrap();

            buf.set_position(0);
            let mut reader = LogReader::new(&mut buf, true);
            let mut dst = Vec::new();
            assert!(reader.read(&mut dst).unwrap());
            assert_eq!(dst, record);
            assert!(!reader.read(&mut dst).unwrap(), "Expected EOF");
        }
    }
}
