use std::{error::Error, fmt::Display};

#[derive(Clone, Debug, PartialEq)]
pub enum StatusCode {
    Ok,

    AlreadyExists,
    Corruption,
    CompressionError,
    IOError,
    InvalidArgument,
    InvalidData,
    LockError,
    NotFound,
    NotSupported,
    PermissionDenied,
    AsyncError,
    Unknown,

    #[cfg(feature = "fs")]
    Errno(errno::Errno),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Status {
    pub code: StatusCode,
    pub err: String,
}

impl Default for Status {
    fn default() -> Self {
        Status {
            code: StatusCode::Ok,
            err: String::new(),
        }
    }
}

impl Display for Status {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.err)
    }
}

impl Error for Status {
    fn description(&self) -> &str {
        &self.err
    }
}

impl Status {
    pub fn new(code: StatusCode, msg: &str) -> Self {
        let err = format!("{:?}: [{}]", code, msg);
        Status { code, err }
    }
}

/// Global result type for the project
pub type Result<T> = std::result::Result<T, Status>;

pub fn err<T>(code: StatusCode, msg: &str) -> Result<T> {
    Err(Status::new(code, msg))
}

impl From<std::io::Error> for Status {
    fn from(err: std::io::Error) -> Self {
        let code = match err.kind() {
            std::io::ErrorKind::NotFound => StatusCode::NotFound,
            std::io::ErrorKind::InvalidData => StatusCode::Corruption,
            std::io::ErrorKind::InvalidInput => StatusCode::InvalidArgument,
            std::io::ErrorKind::PermissionDenied => StatusCode::PermissionDenied,
            _ => StatusCode::IOError,
        };
        Self::new(code, &err.to_string())
    }
}

impl From<snap::Error> for Status {
    fn from(err: snap::Error) -> Self {
        Self {
            code: StatusCode::CompressionError,
            err: err.to_string(),
        }
    }
}

impl<T> From<std::sync::PoisonError<T>> for Status {
    fn from(err: std::sync::PoisonError<T>) -> Self {
        Self::new(StatusCode::LockError, &format!("lock poisoned: [{}]", err))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    mod tests_gpt_4o {
        use super::*;
        use std::io;

        #[test]
        fn test_status_default() {
            let default_status = Status::default();
            assert_eq!(default_status.code, StatusCode::Ok);
            assert_eq!(default_status.err, "");
        }

        #[test]
        fn test_status_new() {
            let status = Status::new(StatusCode::NotFound, "Item not found");
            assert_eq!(status.code, StatusCode::NotFound);
            assert_eq!(status.err, "NotFound: [Item not found]");
        }

        #[test]
        fn test_status_display() {
            let status = Status::new(StatusCode::IOError, "IO error occurred");
            assert_eq!(format!("{}", status), "IOError: [IO error occurred]");
        }

        #[test]
        fn test_status_error() {
            let status = Status::new(StatusCode::InvalidData, "Invalid data provided");
            assert_eq!(status.to_string(), "InvalidData: [Invalid data provided]");
        }

        #[test]
        fn test_result_err() {
            let result: Result<()> = err(StatusCode::PermissionDenied, "Access denied");
            assert!(result.is_err());
            let status = result.unwrap_err();
            assert_eq!(status.code, StatusCode::PermissionDenied);
            assert_eq!(status.err, "PermissionDenied: [Access denied]");
        }

        #[test]
        fn test_from_io_error() {
            let io_err = io::Error::new(io::ErrorKind::NotFound, "file not found");
            let status: Status = io_err.into();
            assert_eq!(status.code, StatusCode::NotFound);
            assert_eq!(status.err, "NotFound: [file not found]");

            let io_err = io::Error::new(io::ErrorKind::InvalidData, "invalid data");
            let status: Status = io_err.into();
            assert_eq!(status.code, StatusCode::Corruption);
            assert_eq!(status.err, "Corruption: [invalid data]");

            let io_err = io::Error::new(io::ErrorKind::PermissionDenied, "permission denied");
            let status: Status = io_err.into();
            assert_eq!(status.code, StatusCode::PermissionDenied);
            assert_eq!(status.err, "PermissionDenied: [permission denied]");

            let io_err = io::Error::new(io::ErrorKind::Other, "other io error");
            let status: Status = io_err.into();
            assert_eq!(status.code, StatusCode::IOError);
            assert_eq!(status.err, "IOError: [other io error]");
        }

        #[test]
        #[cfg(feature = "fs")]
        fn test_from_errno() {
            use errno::Errno;
            let errno = Errno(13);
            let status = Status::new(StatusCode::Errno(errno), "File system error");
            assert_eq!(status.code, StatusCode::Errno(errno));
        }
    }
}
