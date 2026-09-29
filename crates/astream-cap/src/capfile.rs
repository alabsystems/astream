//! The capability FILE: one canonical `<grant> <tag-hex>` line format, and the one
//! reader for it.
//!
//! A cap file holds a node's whole ring, one minted capability per line, in exactly
//! the shape `asb mint` prints — so the file a mint wrote is the file every face
//! reads, and a ring one face accepts is never refused by another:
//!
//! ```text
//! # this node's ring: the fleet's read half, and its own write lane
//! ro:/f/F/pub/>  <64 hex digits>
//! rw,p=n-a1b2c3d4:/f/F/in/*/*/n-a1b2c3d4/*  <64 hex digits>
//! ```
//!
//! THE RULES, and why each is the one:
//!
//! * A line is trimmed. Empty lines, and lines whose first character is `#`, are
//!   skipped. A grant never begins with `#` (it begins with `/`, `rw` or `ro`),
//!   so a comment can never swallow a capability; a comment is a WHOLE line, and a
//!   `#` after the tag is a malformed tag, never a trailing comment.
//! * The line splits at its LAST ASCII whitespace, never its first, because THE
//!   GRANT MAY CONTAIN A SPACE. `Filter::new` rejects only bytes below 0x20 and
//!   0x7f, and 0x20 is neither, so `ro:/f/F/pub a/>` is a legal grant that a mint
//!   seals and prints. Split at the first whitespace, that line read back as the
//!   grant `ro:/f/F/pub` with the tag `a/>`, and the whole ring was refused. The
//!   last whitespace is exact rather than merely better: the tag is the fixed-width
//!   whitespace-free tail, so even a grant that ENDS in a space round-trips.
//! * The grant half must be non-empty. It is otherwise NOT validated here: it is the
//!   string the tag seals, byte for byte, and whether it is a grant at all is
//!   `Grant::parse`'s question, asked where authority is decided.
//! * The tag half is EXACTLY 64 ASCII hex digits, either case: 32 bytes, one
//!   HMAC-SHA256 output. Strict — no sign, no `0x`, no other length — and decoded by
//!   BYTE, so a multibyte character is simply not hex, never a char-boundary panic.
//!   No error message echoes the tag, because the tag is the secret.
//!
//! [`format_line`] writes a line and [`parse_line`] reads one back; [`parse_text`]
//! and [`read_file`] read a whole ring and name `path:line` for the first line that
//! breaks a rule. A ring is all or nothing: one malformed line refuses the file.
//!
//! SELF-CONTAINED ON PURPOSE: std only, nothing from the rest of this crate. `asb`
//! reads `--cap-file` in its DEFAULT build too — a malformed line is a usage error
//! there as well, and only the attach itself needs the MAC — but a default broker
//! does not depend on `astream-cap` (it would pull sha2 into a zero-third-party
//! build), so `asb` compiles THIS FILE into itself by path. Keep it free of
//! `crate::` items and of every dependency: one source, two builds, and no second
//! reader to drift from the first.

use std::fmt;
use std::path::Path;

/// A tag's width in bytes: one HMAC-SHA256 output.
const TAG_BYTES: usize = 32;

/// The digits [`format_line`] writes: lowercase, the one spelling a mint emits.
const HEX: &[u8; 16] = b"0123456789abcdef";

/// One capability line: the grant and the tag that seals it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Line {
    /// The grant, byte for byte as it was minted — the string the tag is over.
    pub grant: String,
    /// The HMAC-SHA256 tag, decoded from the line's 64 hex digits.
    pub tag: [u8; TAG_BYTES],
}

/// Why one line is not a capability line.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// No ASCII whitespace separates a non-empty grant from a tag: the line holds a
    /// grant with no tag, or a tag with no grant.
    Shape,
    /// The tag half is not 64 bytes long; this is the length it has.
    TagLength(usize),
    /// The tag half holds a byte that is not an ASCII hex digit, at this index.
    TagNotHex(usize),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::Shape => f.write_str("expected `<grant> <tag-hex>`"),
            Error::TagLength(n) => write!(
                f,
                "tag: expected {} hex chars ({TAG_BYTES} bytes), got {n} bytes",
                TAG_BYTES * 2
            ),
            Error::TagNotHex(i) => write!(f, "tag: not valid hex at char {i}"),
        }
    }
}

impl std::error::Error for Error {}

/// A malformed line, located — displayed `<path>:<line>: <why>`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Malformed {
    /// Where the text came from, as the caller named it (usually the file's path).
    pub path: String,
    /// The 1-based line number, counting blank and comment lines.
    pub line: usize,
    /// What is wrong with that line.
    pub error: Error,
}

impl fmt::Display for Malformed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}: {}", self.path, self.line, self.error)
    }
}

impl std::error::Error for Malformed {}

/// Why a cap file could not be read into a ring. The two are kept apart because
/// they are different mistakes: a path that is wrong, and a file that is wrong.
#[derive(Debug)]
pub enum ReadError {
    /// The file could not be read at all — absent, unreadable, or not UTF-8.
    /// Displayed `<path>: <error>`.
    Io {
        /// The path, as the caller gave it.
        path: String,
        /// What reading it failed with.
        error: std::io::Error,
    },
    /// The file was read, and a line of it breaks a rule.
    Malformed(Malformed),
}

impl fmt::Display for ReadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReadError::Io { path, error } => write!(f, "{path}: {error}"),
            ReadError::Malformed(m) => m.fmt(f),
        }
    }
}

impl std::error::Error for ReadError {}

/// The one line a cap file holds for a capability: `<grant> <tag-hex>`, the tag as
/// 64 LOWERCASE hex digits after ONE space.
///
/// [`parse_line`] reads it back to the same grant and tag for every grant that is
/// non-empty, starts with neither whitespace nor `#`, and holds no line break —
/// which every string `Grant::parse` accepts does. A space INSIDE the grant, or at
/// its end, is fine: that is what splitting at the last whitespace is for.
#[must_use]
pub fn format_line(grant: &str, tag: &[u8; TAG_BYTES]) -> String {
    let mut line = String::with_capacity(grant.len() + 1 + TAG_BYTES * 2);
    line.push_str(grant);
    line.push(' ');
    for b in tag {
        line.push(char::from(HEX[usize::from(b >> 4)]));
        line.push(char::from(HEX[usize::from(b & 0x0f)]));
    }
    line
}

/// Read one line of a cap file (its terminator may be left on: it is trimmed like
/// any other whitespace). `Ok(None)` for a blank or `#` comment line.
///
/// # Errors
/// [`Error::Shape`] when no ASCII whitespace separates a non-empty grant from a
/// tag; [`Error::TagLength`] / [`Error::TagNotHex`] when the tag is not exactly 64
/// ASCII hex digits. The rules are the module's.
pub fn parse_line(line: &str) -> Result<Option<Line>, Error> {
    let line = line.trim();
    if line.is_empty() || line.starts_with('#') {
        return Ok(None);
    }
    let (grant, tag_hex) = line
        .rsplit_once(|c: char| c.is_ascii_whitespace())
        .filter(|(grant, _)| !grant.is_empty())
        .ok_or(Error::Shape)?;
    Ok(Some(Line {
        grant: grant.to_string(),
        tag: decode_tag(tag_hex.as_bytes())?,
    }))
}

/// Read a whole ring from `text`, in order, skipping blank and comment lines.
/// `path` names the text in an error and is not opened.
///
/// # Errors
/// The FIRST malformed line, as `path:line`; no partial ring is returned.
pub fn parse_text(path: &str, text: &str) -> Result<Vec<Line>, Malformed> {
    text.lines()
        .enumerate()
        .filter_map(|(n, raw)| {
            parse_line(raw)
                .map_err(|error| Malformed {
                    path: path.to_string(),
                    line: n + 1,
                    error,
                })
                .transpose()
        })
        .collect()
}

/// Read a whole ring from the file at `path` — [`parse_text`] over its contents,
/// with errors naming the path as [`Path::display`] shows it.
///
/// # Errors
/// [`ReadError::Io`] when the file cannot be read as UTF-8 text at all;
/// [`ReadError::Malformed`] naming `path:line` for its first malformed line.
pub fn read_file(path: impl AsRef<Path>) -> Result<Vec<Line>, ReadError> {
    let path = path.as_ref();
    let shown = path.display().to_string();
    let text = std::fs::read_to_string(path).map_err(|error| ReadError::Io {
        path: shown.clone(),
        error,
    })?;
    parse_text(&shown, &text).map_err(ReadError::Malformed)
}

/// Decode exactly [`TAG_BYTES`] bytes from 64 ASCII hex digits. Byte-indexed, so a
/// multibyte character is a non-hex byte like any other, never a panic.
fn decode_tag(hex: &[u8]) -> Result<[u8; TAG_BYTES], Error> {
    fn nibble(b: u8) -> Option<u8> {
        match b {
            b'0'..=b'9' => Some(b - b'0'),
            b'a'..=b'f' => Some(b - b'a' + 10),
            b'A'..=b'F' => Some(b - b'A' + 10),
            _ => None,
        }
    }
    if hex.len() != TAG_BYTES * 2 {
        return Err(Error::TagLength(hex.len()));
    }
    let mut tag = [0u8; TAG_BYTES];
    for (i, (out, pair)) in tag.iter_mut().zip(hex.chunks_exact(2)).enumerate() {
        let hi = nibble(pair[0]).ok_or(Error::TagNotHex(2 * i))?;
        let lo = nibble(pair[1]).ok_or(Error::TagNotHex(2 * i + 1))?;
        *out = (hi << 4) | lo;
    }
    Ok(tag)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A tag whose bytes are `base, base+1, …`, so eight of them cover every byte
    /// value once.
    fn tag_from(base: u8) -> [u8; TAG_BYTES] {
        let mut tag = [0u8; TAG_BYTES];
        for (i, b) in tag.iter_mut().enumerate() {
            *b = base.wrapping_add(i as u8);
        }
        tag
    }

    fn hex_of(tag: &[u8; TAG_BYTES]) -> String {
        tag.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// What a mint prints is what the reader reads — for a grant holding a space,
    /// several spaces, or ENDING in one, since the tag is the whitespace-free tail.
    #[test]
    fn a_formatted_line_round_trips_even_when_the_grant_holds_a_space() {
        for grant in [
            "ro:/f/F/pub/>",
            "rw,p=n-a1b2c3d4e5f60718:/f/F/in/*/*/n-a1b2c3d4e5f60718/*",
            "ro:/f/F/pub a/>",
            "ro:/f/F/a  b/c d/>",
            "ro:/f/F/pub a/> ",
            "ro:/f/F/#tag/>",
        ] {
            for base in (0..=u8::MAX).step_by(TAG_BYTES) {
                let tag = tag_from(base);
                let line = format_line(grant, &tag);
                assert_eq!(
                    line,
                    format!("{grant} {}", hex_of(&tag)),
                    "one space, lowercase"
                );
                assert_eq!(
                    parse_line(&line),
                    Ok(Some(Line {
                        grant: grant.to_string(),
                        tag
                    })),
                    "{line:?}"
                );
            }
        }
        // Uppercase hex is read too; only the writer is lowercase.
        let upper = format!("ro:/f/F/> {}", "AB".repeat(TAG_BYTES));
        assert_eq!(parse_line(&upper).unwrap().unwrap().tag, [0xab; TAG_BYTES]);
    }

    /// Blank and `#` lines are skipped, and ONLY those: a `#` inside a grant is a
    /// grant, and a `#` after the tag is a malformed tag, not a trailing comment.
    #[test]
    fn blank_and_comment_lines_are_skipped_and_nothing_else_is() {
        let tag = hex_of(&tag_from(7));
        let commented_out = format!("#ro:/f/F/> {tag}");
        for skipped in [
            "",
            "   ",
            "\t \r",
            "#",
            "# the ring",
            "   # indented",
            commented_out.as_str(),
        ] {
            assert_eq!(parse_line(skipped), Ok(None), "{skipped:?}");
        }
        assert!(parse_line(&format!("ro:/f/#/> {tag}")).unwrap().is_some());
        assert_eq!(
            parse_line(&format!("ro:/f/F/> {tag} # note")),
            Err(Error::TagLength(4))
        );
        // Surrounding whitespace and a CR are trimmed, not read as grant or tag.
        let padded = parse_line(&format!("  ro:/f/F/>\t{tag}  \r"))
            .unwrap()
            .unwrap();
        assert_eq!(padded.grant, "ro:/f/F/>");
        assert_eq!(padded.tag, tag_from(7));
    }

    /// A grant with no tag, and a tag with no grant, are the same shape error — and
    /// so is a line whose only separator is NON-ASCII whitespace: a mint writes one
    /// ASCII space, and the separator is ASCII whitespace only.
    #[test]
    fn a_line_missing_either_half_is_a_shape_error() {
        let tag = hex_of(&tag_from(0));
        let indented = format!("  {tag}");
        let nbsp = format!("ro:/f/F/>\u{a0}{tag}");
        let ideographic = format!("ro:/f/F/>\u{3000}{tag}");
        for bad in [
            "ro:/f/F/>",
            "ro:/f/F/>   ",
            tag.as_str(),
            indented.as_str(),
            nbsp.as_str(),
            ideographic.as_str(),
        ] {
            assert_eq!(parse_line(bad), Err(Error::Shape), "{bad:?}");
        }
    }

    /// The tag is EXACTLY 32 bytes of strict hex. Every refusal is an error, never
    /// a panic, and no error message echoes the tag it refused.
    #[test]
    fn the_tag_is_exactly_32_bytes_of_strict_hex() {
        let good = hex_of(&tag_from(0x40));
        for n in [2, 62, 63, 65, 66, 128] {
            let tag: String = good.chars().cycle().take(n).collect();
            let e = parse_line(&format!("ro:/f/F/> {tag}")).unwrap_err();
            assert_eq!(e, Error::TagLength(n), "{n} digits");
            assert!(
                !e.to_string().contains(&tag),
                "the refusal echoes the tag: {e}"
            );
        }
        let cases = [
            ("zz".repeat(TAG_BYTES), 0),
            (format!("0g{}", &good[2..]), 1),
            ("+f".repeat(TAG_BYTES), 0),
            ("-1".repeat(TAG_BYTES), 0),
            (format!("0x{}", &good[2..]), 1),
            // Multibyte: 64 BYTES of valid UTF-8, so the length check passes and
            // the decoder meets a byte of a character, not a char boundary.
            (format!("é{}", &good[2..]), 0),
            (format!("{}é{}", &good[..31], &good[33..]), 31),
            (format!("{}é{}", &good[..32], &good[34..]), 32),
            (format!("{}é", &good[..62]), 62),
        ];
        for (tag, at) in cases {
            assert_eq!(tag.len(), TAG_BYTES * 2, "{tag:?} is 64 bytes");
            let e = parse_line(&format!("ro:/f/F/> {tag}")).unwrap_err();
            assert_eq!(e, Error::TagNotHex(at), "{tag:?}");
            assert!(e.to_string().starts_with("tag: not valid hex"), "{e}");
        }
    }

    /// A ring reads in order, skipping blanks and comments; the first bad line
    /// refuses the whole text and is named `path:line`, counting every line.
    #[test]
    fn parse_text_reads_a_ring_and_names_path_and_line() {
        let (a, b) = (tag_from(1), tag_from(2));
        let ring = format!(
            "# node ring\n\nro:/f/F/pub a/> {}\r\n  rw,p=n-a1:/f/F/in/n-a1/> {}\n",
            hex_of(&a),
            hex_of(&b)
        );
        assert_eq!(
            parse_text("node.cap", &ring),
            Ok(vec![
                Line {
                    grant: "ro:/f/F/pub a/>".to_string(),
                    tag: a
                },
                Line {
                    grant: "rw,p=n-a1:/f/F/in/n-a1/>".to_string(),
                    tag: b
                },
            ])
        );
        assert_eq!(parse_text("empty.cap", "\n# nothing\n"), Ok(vec![]));

        let bad = format!("{ring}# next\nro:/f/F/>\nro:/f/F/> zz\n");
        let e = parse_text("node.cap", &bad).unwrap_err();
        assert_eq!(
            e,
            Malformed {
                path: "node.cap".to_string(),
                line: 6,
                error: Error::Shape
            }
        );
        assert_eq!(e.to_string(), "node.cap:6: expected `<grant> <tag-hex>`");
    }

    /// The file reader: `path:line` for a malformed line, and a read error naming
    /// the path — distinct from a malformed one — for a file it cannot read.
    #[test]
    fn read_file_names_path_and_line_and_keeps_a_read_error_distinct() {
        let dir = std::env::temp_dir().join(format!("astream-capfile-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let tag = tag_from(9);

        let good = dir.join("good.cap");
        std::fs::write(
            &good,
            format!("# ring\n{}\n", format_line("ro:/f/F/ a/>", &tag)),
        )
        .unwrap();
        assert_eq!(
            read_file(&good).unwrap(),
            vec![Line {
                grant: "ro:/f/F/ a/>".to_string(),
                tag
            }]
        );

        let bad = dir.join("bad.cap");
        std::fs::write(&bad, format!("\nro:/f/F/> {}\n", "zz".repeat(TAG_BYTES))).unwrap();
        let e = read_file(&bad).unwrap_err();
        assert!(
            matches!(&e, ReadError::Malformed(m) if m.line == 2 && m.error == Error::TagNotHex(0)),
            "{e:?}"
        );
        assert_eq!(
            e.to_string(),
            format!("{}:2: tag: not valid hex at char 0", bad.display())
        );

        let missing = dir.join("missing.cap");
        let e = read_file(&missing).unwrap_err();
        assert!(matches!(&e, ReadError::Io { .. }), "{e:?}");
        assert!(
            e.to_string()
                .starts_with(&format!("{}: ", missing.display())),
            "{e}"
        );

        let binary = dir.join("binary.cap");
        std::fs::write(&binary, [b'r', b'o', 0xff, b'\n']).unwrap();
        assert!(matches!(read_file(&binary), Err(ReadError::Io { .. })));

        let _ = std::fs::remove_dir_all(&dir);
    }
}
