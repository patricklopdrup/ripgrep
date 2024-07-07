use std::time::{Duration, SystemTime};

/// An error that occurs when parsing a human readable size description.
///
/// This error provides an end user friendly message describing why the
/// description couldn't be parsed and what the expected format is.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseSizeError {
    original: String,
    kind: ParseSizeErrorKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ParseSizeErrorKind {
    InvalidFormat,
    InvalidInt(std::num::ParseIntError),
    Overflow,
}

impl ParseSizeError {
    fn format(original: &str) -> ParseSizeError {
        ParseSizeError {
            original: original.to_string(),
            kind: ParseSizeErrorKind::InvalidFormat,
        }
    }

    fn int(original: &str, err: std::num::ParseIntError) -> ParseSizeError {
        ParseSizeError {
            original: original.to_string(),
            kind: ParseSizeErrorKind::InvalidInt(err),
        }
    }

    fn overflow(original: &str) -> ParseSizeError {
        ParseSizeError {
            original: original.to_string(),
            kind: ParseSizeErrorKind::Overflow,
        }
    }
}

impl std::error::Error for ParseSizeError {}

impl std::fmt::Display for ParseSizeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use self::ParseSizeErrorKind::*;

        match self.kind {
            InvalidFormat => write!(
                f,
                "invalid format for size '{}', which should be a non-empty \
                 sequence of digits followed by an optional 'K', 'M' or 'G' \
                 suffix",
                self.original
            ),
            InvalidInt(ref err) => write!(
                f,
                "invalid integer found in size '{}': {}",
                self.original, err
            ),
            Overflow => write!(f, "size too big in '{}'", self.original),
        }
    }
}

impl From<ParseSizeError> for std::io::Error {
    fn from(size_err: ParseSizeError) -> std::io::Error {
        std::io::Error::new(std::io::ErrorKind::Other, size_err)
    }
}


/// An error that occurs when parsing a human readable time description.
///
/// This error provides an end user friendly message describing why the
/// description couldn't be parsed and what the expected format is.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParseTimeError {
    original: String,
    kind: ParseTimeErrorKind,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ParseTimeErrorKind {
    InvalidFormat,
    InvalidInt(std::num::ParseIntError),
    Overflow,
}

impl ParseTimeError {
    fn format(original: &str) -> ParseTimeError {
        ParseTimeError {
            original: original.to_string(),
            kind: ParseTimeErrorKind::InvalidFormat,
        }
    }

    fn int(original: &str, err: std::num::ParseIntError) -> ParseTimeError {
        ParseTimeError {
            original: original.to_string(),
            kind: ParseTimeErrorKind::InvalidInt(err),
        }
    }

    fn overflow(original: &str) -> ParseTimeError {
        ParseTimeError {
            original: original.to_string(),
            kind: ParseTimeErrorKind::Overflow,
        }
    }
}

impl std::error::Error for ParseTimeError {}

impl std::fmt::Display for ParseTimeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use self::ParseTimeErrorKind::*;

        match self.kind {
            InvalidFormat => write!(
                f,
                "invalid format for time '{}', which should be a non-empty \
                 sequence of digits followed by an optional 'm', 'h', or \
                 'd' suffix",
                self.original
            ),
            InvalidInt(ref err) => write!(
                f,
                "invalid integer found in time '{}': {}",
                self.original, err
            ),
            Overflow => write!(f, "time too big in '{}'", self.original),
        }
    }
}

impl From<ParseTimeError> for std::io::Error {
    fn from(time_err: ParseTimeError) -> std::io::Error {
        std::io::Error::new(std::io::ErrorKind::Other, time_err)
    }
}

/// Parse a human readable size like `2M` into a corresponding number of bytes.
///
/// Supported size suffixes are `K` (for kilobyte), `M` (for megabyte) and `G`
/// (for gigabyte). If a size suffix is missing, then the size is interpreted
/// as bytes. If the size is too big to fit into a `u64`, then this returns an
/// error.
///
/// Additional suffixes may be added over time.
pub fn parse_human_readable_size(size: &str) -> Result<u64, ParseSizeError> {
    let digits_end =
        size.as_bytes().iter().take_while(|&b| b.is_ascii_digit()).count();
    let digits = &size[..digits_end];
    if digits.is_empty() {
        return Err(ParseSizeError::format(size));
    }
    let value =
        digits.parse::<u64>().map_err(|e| ParseSizeError::int(size, e))?;

    let suffix = &size[digits_end..];
    if suffix.is_empty() {
        return Ok(value);
    }
    let bytes = match suffix {
        "K" => value.checked_mul(1 << 10),
        "M" => value.checked_mul(1 << 20),
        "G" => value.checked_mul(1 << 30),
        _ => return Err(ParseSizeError::format(size)),
    };
    bytes.ok_or_else(|| ParseSizeError::overflow(size))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suffix_none() {
        let x = parse_human_readable_size("123").unwrap();
        assert_eq!(123, x);
    }

    #[test]
    fn suffix_k() {
        let x = parse_human_readable_size("123K").unwrap();
        assert_eq!(123 * (1 << 10), x);
    }

    #[test]
    fn suffix_m() {
        let x = parse_human_readable_size("123M").unwrap();
        assert_eq!(123 * (1 << 20), x);
    }

    #[test]
    fn suffix_g() {
        let x = parse_human_readable_size("123G").unwrap();
        assert_eq!(123 * (1 << 30), x);
    }

    #[test]
    fn invalid_empty() {
        assert!(parse_human_readable_size("").is_err());
    }

    #[test]
    fn invalid_non_digit() {
        assert!(parse_human_readable_size("a").is_err());
    }

    #[test]
    fn invalid_overflow() {
        assert!(parse_human_readable_size("9999999999999999G").is_err());
    }

    #[test]
    fn invalid_suffix() {
        assert!(parse_human_readable_size("123T").is_err());
    }
}

/// Parse a human readable relative time like `2d` into the corresponding seconds
/// since UNIX_EPOCH.
///
/// Supported relative time suffixes are `m` (for minute), `h` (for hour), `d`
/// (for day), `w` (for week). If a relative time suffix is missing, then the
/// it is interpreted as seconds. If the inputted relative time is too big to
/// fit into a `u64`, then this returns an error.
///
/// Additional suffixes may be added over time.
pub fn parse_human_readable_time(time: &str) -> Result<u64, ParseTimeError> {
    let sys_time_now = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH);
    match sys_time_now {
        Ok(dur) => parse_epoch_time_from_duration(time, &dur),
        Err(e) => Err(ParseTimeError::format(&e.to_string()))
    }
}

fn parse_epoch_time_from_duration(time_input: &str, duration_epoch: &Duration) -> Result<u64, ParseTimeError> {
    let unix_time_seconds = duration_epoch.as_secs();

    let digits_end =
        time_input.as_bytes().iter().take_while(|&b| b.is_ascii_digit()).count();
    let digits = &time_input[..digits_end];
    if digits.is_empty() {
        return Err(ParseTimeError::format(time_input));
    }
    let value =
        digits.parse::<u64>().map_err(|e| ParseTimeError::int(time_input, e))?;

    let suffix = &time_input[digits_end..];
    if suffix.is_empty() {
        return unix_time_seconds.checked_sub(value)
            .ok_or_else(|| ParseTimeError::overflow(time_input));
    }
    let seconds = match suffix {
        "m" => value.checked_mul(60),
        "h" => value.checked_mul(60 * 60),
        "d" => value.checked_mul(60 * 60 * 24),
        "w" => value.checked_mul(60 * 60 * 24 * 7),
        _ => return Err(ParseTimeError::format(time_input))
    };

    if let Some(seconds) = seconds {
        unix_time_seconds.checked_sub(seconds)
            .ok_or_else(|| ParseTimeError::overflow(time_input))
    } else {
        Err(ParseTimeError::overflow(time_input))
    }
}

#[cfg(test)]
mod tests_date {
    use super::*;
    const JAN_1ST_2024_EPOCH: u64 = 1704067200;
    const DATE: Duration = Duration::from_secs(JAN_1ST_2024_EPOCH);

    #[test]
    fn suffix_none() {
        let x = parse_epoch_time_from_duration("123", &DATE).unwrap();
        assert_eq!(JAN_1ST_2024_EPOCH - 123, x);
    }

    #[test]
    fn suffix_m() {
        let x = parse_epoch_time_from_duration("123m", &DATE).unwrap();
        assert_eq!(JAN_1ST_2024_EPOCH - (123 * 60), x);
    }

    #[test]
    fn suffix_h() {
        let x = parse_epoch_time_from_duration("123h", &DATE).unwrap();
        assert_eq!(JAN_1ST_2024_EPOCH - (123 * 60 * 60), x);
    }

    #[test]
    fn suffix_d() {
        let x = parse_epoch_time_from_duration("123d", &DATE).unwrap();
        assert_eq!(JAN_1ST_2024_EPOCH - (123 * 60 * 60 * 24), x);
    }

    #[test]
    fn invalid_empty() {
        assert!(parse_epoch_time_from_duration("", &DATE).is_err());
    }

    #[test]
    fn invalid_non_digit() {
        assert!(parse_epoch_time_from_duration("a", &DATE).is_err());
    }

    #[test]
    fn invalid_overflow() {
        assert!(parse_epoch_time_from_duration("9999999999999999d", &DATE).is_err());
    }

    #[test]
    fn invalid_suffix() {
        assert!(parse_epoch_time_from_duration("123X", &DATE).is_err());
    }
}