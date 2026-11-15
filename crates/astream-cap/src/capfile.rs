//! The capability FILE: one canonical `<grant> <tag-hex>` line format, and the one
//! reader for it; and the SECRET FILE rule every file of key material is read by.
//!
//! Two rules live here, for one reason: they are the two that every face of astream
//! reads off disk, and both used to be written again by each face that read them.
//! The line format is below. The secret-file rule ([`check_private`],
//! [`read_private_file`], [`read_secret_file`], [`read_secret_in`], [`read_secret_at`],
//! [`read_secret_at_narrowed`], [`SECRET_MIN`]), judged through astream-sys's owner-only rule, is at the end of this doc,
//! and [`read_private_ring`] holds a ring to it.
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
//! SELF-CONTAINED ON PURPOSE: std and astream-sys only, nothing from the rest of
//! this crate. `asb` reads `--cap-file` in its DEFAULT build too — a malformed line
//! is a usage error there as well, and only the attach itself needs the MAC — but a
//! default broker does not depend on `astream-cap` (capabilities are its opt-in
//! `cap` feature), so `asb` compiles THIS FILE into itself by path, and so does
//! `aspump`. Keep it free of `crate::` items and of every dependency but
//! astream-sys (the OS cordon, zero-dependency itself, which astream-broker and
//! astream-pump depend on directly): one source, three builds, and no second reader
//! to drift from the first.
//!
//! THE SECRET FILE. A mint secret (what `Broker::open_guarded` seals and verifies
//! with), a pre-shared transport key and a cap file all hold material that IS
//! authority: whoever reads one can mint, decrypt or attach as its owner. The rule
//! for reading one, and why each clause is the one:
//!
//! * NON-BLOCKING OPEN: the file is opened read-only with `O_NONBLOCK`
//!   ([`astream_sys::open_nonblocking`]), so whatever sits at the path opens at once.
//!   A plain open of a FIFO waits until something opens its other end: a reader
//!   that opened before it judged would hang on one anyone who can write the
//!   directory can make with `mkfifo`. The FIFO is then refused by the next clause.
//! * OWNER-ONLY, judged on the open descriptor by astream-sys's one rule
//!   ([`astream_sys::owner_private`], [`check_private`]), clause by clause: a
//!   REGULAR file (a directory, a FIFO, a socket or a device is `InvalidInput`);
//!   OWNED by this process's effective uid (another user decides who reads it);
//!   `mode & 0o077 == 0`, 0600 or tighter; and on macOS NO ACCESS-LIST ENTRY THAT
//!   ALLOWS anyone anything, because macOS checks an extended ACL before the mode
//!   bits, so a 0600 file with an `everyone allow read` entry (one a parent's
//!   `file_inherit` entry passed on, say) is open to every user. A deny entry takes
//!   nothing away and passes. On Linux a POSIX ACL that grants anyone shows in the
//!   group mode bits, which the mode clause reads. The refusal names the `chmod`
//!   (`chmod 600`, `chmod -N`) rather than fixing the file silently, because a key
//!   that sat readable may already have been read, and the person who owns it
//!   should know that. Off Unix only the kind is checked (there are no mode bits),
//!   and, for a secret, its length.
//! * ONE OPEN: every clause is read off the OPEN file (`fstat` on the descriptor), and a
//!   reader returns the bytes of that same descriptor. A check by path followed by
//!   a read by path resolves the path twice, and whoever can write the directory
//!   can swap a 0600 file for a link to a 0644 one between the two: the check
//!   passes on one file and the key comes from another. So nothing here stats a
//!   path ([`check_private`] opens it too), and a face that READS a secret goes
//!   through [`read_private_file`] or [`read_secret_file`], never a check and then
//!   its own read.
//! * A SECRET IN A DIRECTORY OF ITS OWN ([`read_secret_in`], and [`read_secret_at`]
//!   over one path's directory and name): the directory is opened without following
//!   a link and held to the same owner-only rule as a directory (0700 or tighter,
//!   ours, no ACL allow entry), because whoever can write it can replace the secret
//!   or give it a second name; the name is one path component; the file is opened
//!   without following a link (`O_NOFOLLOW`) and must have ONE link, because a
//!   second name for it may sit in a directory others can reach. The directory's
//!   refusal names the `chmod` that closes it but does not call the secret exposed:
//!   a directory others can open or write lets them replace the secret, not read it,
//!   and the file's own clauses, judged next, say whether others could read it.
//!   [`read_secret_at_narrowed`] is the dry run of a caller that narrows the
//!   directory's mode before it reads. The path readers ([`read_private_file`],
//!   [`read_secret_file`]) still follow a link at the path: an operator who points
//!   `asb --secret-file` at one keeps working.
//! * EXACT BYTES ([`read_private_file`], [`read_secret_file`]): the secret is every
//!   byte the file holds, a trailing newline or space included. A mint secret is
//!   `head -c 32 /dev/urandom`, raw random bytes that begin or end with a whitespace
//!   byte about one time in twenty-five, and the broker that verifies and the verb
//!   that mints must seal with the same key: a reader that trimmed sealed a
//!   different secret from one that did not, silently.
//! * AT LEAST [`SECRET_MIN`] = 32 bytes ([`read_secret_file`]): HMAC takes a key of
//!   any length, so an empty or truncated secret mints capabilities that look
//!   well-formed and seal nothing.
//! * PATH-FIRST REFUSALS, as `io::Error`s whose kind says which clause broke:
//!   `NotFound` (the file is not there, which a caller may answer with a hint),
//!   `PermissionDenied` (another owner, a group/other bit, an ACL allow entry, a
//!   symlink or a second link where [`read_secret_in`] refuses them, or an OS
//!   refusal to open it), `InvalidInput` (not a regular file, a directory that is no
//!   directory, a name of more than one component, or a path that names no file)
//!   and `InvalidData` (too short). Every message starts with the path, once, as its
//!   caller spelled it (a bare name is not `./<name>`): an OS error, which never
//!   names one, is re-wrapped as `<path>: <error>` with its kind kept, so a caller
//!   prefixes only its own flag (`--secret-file {e}`) and never names the path twice.
//!
//! `asb` reads `--secret-file` through [`read_secret_file`], and `serve` reads the
//! `--key-file` it serves under through [`read_private_file`] (the key is hex, so
//! `asb` trims and decodes it, and its own decoder holds it to 32 bytes). aterm's
//! fabric reads its `mint.secret` through [`read_secret_at`] (its
//! `read_mint_secret`, for `aterm link broker --secret-file`, `aterm link mint` and
//! `aterm fabric on`/`mint-for`), so the broker that verifies and the verb that mints
//! read a secret by this one code, and `fabric on --dry-run` through
//! [`read_secret_at_narrowed`] when its root step would narrow the root.
//!
//! A cap file is read one of two ways, and the face that reads it says which. [`read_file`]
//! does NOT check a cap file's mode, and is what `asb` and `aspump` read `--cap-file` by: an
//! operator's tool reads the ring it is pointed at, a process substitution included.
//! [`read_private_ring`] holds the ring to the owner-only rule on the file itself, refusing a
//! link at the path too, and is what aterm's fabric reads every cap by
//! (`bridge::read_cap_file`). The directory, the link count and the length floor are clauses of
//! a secret in a directory of its own, and it holds none of them: a person keeps a cap where
//! they choose, `~/h-andrew.cap` in a home directory of 0750, say.

use std::fmt;
use std::io::Read;
use std::path::Path;

#[cfg(clean_islands)]
#[path = "capfile_island.rs"]
mod capfile_island;
#[cfg(clean_islands)]
pub use capfile_island::capfile_line_advance;

/// `capfile_line_advance` as `capfile_island.rs` defines it in Clean:
/// `if cur < cand then cand else cur`.
#[cfg(not(clean_islands))]
#[must_use]
pub const fn capfile_line_advance(cur: u64, cand: u64) -> u64 {
    if cur < cand {
        cand
    } else {
        cur
    }
}

contract_fn! {
    /// Verified check that a capability tag hex slice is 64 ASCII bytes (`len == 64`),
    /// linked via `clean-kernel-defeq` to `capfile_tag_hex_len_valid_isl`.
    #[must_use]
    pub const fn capfile_tag_hex_len_valid(len: usize) -> bool
    clauses [ensures result == (len == 64)]
    {
        len == 64
    }
}

/// A tag's width in bytes: one HMAC-SHA256 output.
pub(crate) const TAG_BYTES: usize = 32;

/// The digits [`format_line`] writes: lowercase, the one spelling a mint emits.
const HEX: &[u8; 16] = b"0123456789abcdef";

/// One capability line: the grant and the tag that seals it.
///
/// Its `Debug` output names the grant but redacts the tag, as `Capability`'s does:
/// the tag IS the bearer secret, and debug output ends up in logs.
#[derive(Clone, PartialEq, Eq)]
pub struct Line {
    /// The grant, byte for byte as it was minted — the string the tag is over.
    pub grant: String,
    /// The HMAC-SHA256 tag, decoded from the line's 64 hex digits.
    pub tag: [u8; TAG_BYTES],
}

impl fmt::Debug for Line {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Line")
            .field("grant", &self.grant)
            .field("tag", &"<redacted>")
            .finish()
    }
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

#[inline]
const fn write_hex_byte(out: &mut [u8; 2], b: u8) {
    out[0] = HEX[(b >> 4) as usize];
    out[1] = HEX[(b & 0x0f) as usize];
}

/// The one line a cap file holds for a capability: `<grant> <tag-hex>`, the tag as
/// 64 LOWERCASE hex digits after ONE space.
///
/// [`parse_line`] reads it back to the same grant and tag for every grant that is
/// non-empty, starts with neither whitespace nor `#`, and holds no line break —
/// which every string `Grant::parse` accepts does. A space INSIDE the grant, or at
/// its end, is fine: that is what splitting at the last whitespace is for.
#[must_use]
pub fn format_line(grant: &str, tag: &[u8; TAG_BYTES]) -> String {
    // The copy of `grant` sizes itself; only the constant-size tail is reserved,
    // so no length sum of ours can overflow.
    const TAIL: usize = 1 + TAG_BYTES * 2;
    let mut line = grant.to_owned();
    line.reserve(TAIL);
    line.push(' ');
    let mut pair = [0u8; 2];
    let mut i = 0usize;
    while i < TAG_BYTES {
        write_hex_byte(&mut pair, tag[i]);
        if let Ok(s) = std::str::from_utf8(&pair) {
            line.push_str(s);
        }
        i += 1;
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
    let Some((grant, tag_hex)) = line.rsplit_once([' ', '\t', '\n', '\r', '\x0c']) else {
        return Err(Error::Shape);
    };
    if grant.is_empty() {
        return Err(Error::Shape);
    }
    match decode_tag(tag_hex.as_bytes()) {
        Ok(tag) => Ok(Some(Line {
            grant: grant.to_string(),
            tag,
        })),
        Err(e) => Err(e),
    }
}

/// Read a whole ring from `text`, in order, skipping blank and comment lines.
/// `path` names the text in an error and is not opened.
///
/// # Errors
/// The FIRST malformed line, as `path:line`; no partial ring is returned.
pub fn parse_text(path: &str, text: &str) -> Result<Vec<Line>, Malformed> {
    let mut out = Vec::new();
    let mut line_no = 0usize;
    for raw in text.lines() {
        let next_no = line_no.saturating_add(1) as u64;
        line_no = capfile_line_advance(line_no as u64, next_no) as usize;
        match parse_line(raw) {
            Ok(Some(item)) => out.push(item),
            Ok(None) => {}
            Err(error) => {
                return Err(Malformed {
                    path: path.to_string(),
                    line: line_no,
                    error,
                });
            }
        }
    }
    Ok(out)
}

/// Read a whole ring from the file at `path` — [`parse_text`] over its contents,
/// with errors naming the path as [`Path::display`] shows it. This is a plain read: the
/// secret-file rule below does not reach it, so a ring at 0644 is read, and a FIFO at
/// `path` waits for a writer. Whoever keeps a ring keeps it private, and a face that holds
/// its rings private reads them with [`read_private_ring`].
///
/// # Errors
/// [`ReadError::Io`] when the file cannot be read as UTF-8 text at all;
/// [`ReadError::Malformed`] naming `path:line` for its first malformed line.
pub fn read_file(path: impl AsRef<Path>) -> Result<Vec<Line>, ReadError> {
    let path = path.as_ref();
    let shown = path.display().to_string();
    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(error) => {
            return Err(ReadError::Io { path: shown, error });
        }
    };
    let text = match core::str::from_utf8(&bytes) {
        Ok(t) => t,
        Err(e) => {
            return Err(ReadError::Io {
                path: shown,
                error: std::io::Error::new(std::io::ErrorKind::InvalidData, e),
            });
        }
    };
    match parse_text(&shown, text) {
        Ok(lines) => Ok(lines),
        Err(m) => Err(ReadError::Malformed(m)),
    }
}

/// The shortest secret [`read_secret_file`] returns, in bytes. HMAC takes a key of
/// any length, so an empty or truncated secret file mints capabilities that look
/// perfectly well-formed and seal nothing: the failure is a fleet that appears
/// configured and is not. 32 bytes is what a generated secret is (`head -c 32
/// /dev/urandom`), and what `asb` and the aterm fabric have always refused below.
pub const SECRET_MIN: usize = 32;

/// `e`, re-wrapped so its message starts with `path`: an OS error never names the
/// path it failed on. The kind is kept, so `NotFound` stays `NotFound`.
fn at_path(path: &Path, e: std::io::Error) -> std::io::Error {
    std::io::Error::new(e.kind(), format!("{}: {e}", path.display()))
}

/// A refusal of `path`: `kind`, and a message that starts with the path.
fn refused(path: &Path, kind: std::io::ErrorKind, why: &str) -> std::io::Error {
    std::io::Error::new(kind, format!("{}{why}", path.display()))
}

/// Which clause of the owner-only rule a reader here refused a file for ([`refusal_of`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// A symlink where the reader follows none.
    Link,
    /// A clause astream-sys judges off the open file ([`astream_sys::owner_private`]).
    File(astream_sys::NotPrivate),
}

/// The words of a [`Refusal`] and the clause they say, as an [`std::io::Error`] carries them.
#[derive(Debug)]
struct RuleRefused {
    said: String,
    clause: Refusal,
}

impl fmt::Display for RuleRefused {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.said)
    }
}

impl std::error::Error for RuleRefused {}

/// The clause of the owner-only rule `error` says, for a caller that acts on a refusal rather
/// than only printing it, and `None` for anything else this module answers. An open the OS
/// refused is `PermissionDenied` too (a file of mode 000, another user's 0600), and so is a clause
/// of the rule: only this tells a file the reader cannot open from one the rule will not take. A
/// refusal of the DIRECTORY that holds a secret, or of a file's link count, names no clause here.
#[must_use]
pub fn refusal_of(error: &std::io::Error) -> Option<Refusal> {
    let refused = error.get_ref()?.downcast_ref::<RuleRefused>()?;
    Some(refused.clause)
}

/// [`refused`] for the clause `clause`, which [`refusal_of`] then reads back.
fn refused_by(path: &Path, kind: std::io::ErrorKind, why: &str, clause: Refusal) -> std::io::Error {
    let said = format!("{}{why}", path.display());
    std::io::Error::new(kind, RuleRefused { said, clause })
}

/// The owner-only rule's refusal of the FILE at `path` (astream-sys's clause, worded
/// for the person who owns the secret). A mode or an access list names the command
/// that closes it rather than closing it silently: a key that sat readable may
/// already have been read.
fn file_refusal(path: &Path, why: astream_sys::NotPrivate) -> std::io::Error {
    use astream_sys::NotPrivate;
    use std::io::ErrorKind::{InvalidInput, PermissionDenied};
    let shown = path.display();
    let refused = |kind, words: &str| refused_by(path, kind, words, Refusal::File(why));
    match why {
        NotPrivate::Mode(mode) => refused(
            PermissionDenied,
            &format!(
                " is mode {mode:04o}: a secret file must be readable by its owner alone \
                 (0600 or tighter); run `chmod 600 {shown}` and treat its contents as exposed"
            ),
        ),
        NotPrivate::Acl => refused(
            PermissionDenied,
            &format!(
                " {why}: a secret file must be readable by its owner alone; run `chmod -N \
                 {shown}` and treat its contents as exposed"
            ),
        ),
        NotPrivate::Owner(_) => refused(
            PermissionDenied,
            &format!(" {why}: a secret file is its reader's own"),
        ),
        NotPrivate::Kind(_) => refused(
            InvalidInput,
            &format!(" {why}: a secret file is a regular file"),
        ),
    }
}

/// The refusal of the DIRECTORY `dir` that holds the secret at `path`
/// ([`read_secret_in`]): it leads with the secret's path, as every refusal here does.
fn dir_refusal(path: &Path, dir: &Path, why: astream_sys::NotPrivate) -> std::io::Error {
    use astream_sys::NotPrivate;
    use std::io::ErrorKind::{InvalidInput, PermissionDenied};
    let dir = dir.display();
    match why {
        NotPrivate::Mode(mode) => refused(
            path,
            PermissionDenied,
            &format!(
                ": its directory {dir} is mode {mode:04o}: a secret's directory must be its \
                 owner's alone (0700), so that nobody else can replace the secret or give it \
                 a second name; run `chmod 700 {dir}`"
            ),
        ),
        NotPrivate::Acl => refused(
            path,
            PermissionDenied,
            &format!(
                ": its directory {dir} {why}: a secret's directory must be its owner's alone, \
                 so that nobody else can replace the secret or give it a second name; run \
                 `chmod -N {dir}`"
            ),
        ),
        NotPrivate::Owner(_) => refused(
            path,
            PermissionDenied,
            &format!(": its directory {dir} {why}: a secret's directory is its reader's own"),
        ),
        NotPrivate::Kind(_) => refused(
            path,
            InvalidInput,
            &format!(": its directory {dir} {why}, not a directory"),
        ),
    }
}

/// Whether `path` names a symbolic link: what an open under [`astream_sys::Links::Refuse`]
/// that failed found there. Asked only to word that refusal; the open alone decided it.
fn is_link(path: &Path) -> bool {
    std::fs::symlink_metadata(path).is_ok_and(|m| m.file_type().is_symlink())
}

/// Open `path` read-only and non-blocking and hold the open file to the owner-only
/// rule, read off the descriptor ([`astream_sys::owner_private`]): the one open every
/// function below starts from, so a clause is never checked on one file and the
/// bytes read from another. `links` says whether a symlink at the last component is
/// followed (the path API, which `asb --secret-file` users point at a link) or
/// refused ([`read_secret_in`]).
fn open_private(
    path: &Path,
    links: astream_sys::Links,
) -> std::io::Result<(std::fs::File, std::fs::Metadata)> {
    open_private_as(path, path, links, SECRET_NO_LINK)
}

/// Why a secret in a private directory refuses a link at its path.
const SECRET_NO_LINK: &str =
    " is a symlink: a secret in a private directory is read through no link";

/// Why [`read_private_ring`] refuses a link at its path, and what to do.
const RING_NO_LINK: &str = " is a symlink: a private ring is read through no link, so name the \
                            file it points at";

/// [`open_private`] of the file at `at`, every refusal naming it as `path`: the
/// spelling its caller was given ([`read_secret_at`] opens a bare name's file beneath
/// `.` and names it as given). `no_link` follows the path in the refusal of a link there.
fn open_private_as(
    at: &Path,
    path: &Path,
    links: astream_sys::Links,
    no_link: &str,
) -> std::io::Result<(std::fs::File, std::fs::Metadata)> {
    let file = match astream_sys::open_nonblocking(at, links) {
        Ok(file) => file,
        Err(_) if links == astream_sys::Links::Refuse && is_link(at) => {
            return Err(refused_by(
                path,
                std::io::ErrorKind::PermissionDenied,
                no_link,
                Refusal::Link,
            ));
        }
        Err(e) => return Err(at_path(path, e)),
    };
    match astream_sys::owner_private(&file).map_err(|e| at_path(path, e))? {
        Ok(meta) => Ok((file, meta)),
        Err(why) => Err(file_refusal(path, why)),
    }
}

/// Refuse a SECRET file anyone but its owner can read: a mint secret, a
/// pre-shared key, a cap file. It must be a regular file of this user's, 0600 or
/// tighter, with no access-list entry that lets anyone else in; the rules are the
/// module's.
///
/// It OPENS the file (read-only, non-blocking) and judges the open descriptor, as
/// the readers do, rather than `stat`ing the path. A check is still only a check
/// of a moment: a caller that then opens the path again reads whatever the path
/// names by then, so a face that reads the file uses [`read_private_file`] or
/// [`read_secret_file`] instead of this and its own read.
///
/// # Errors
///
/// The open (`NotFound` when the file is not there, `PermissionDenied` when the OS
/// refuses to open it), `PermissionDenied` naming the mode and the `chmod` that
/// fixes it, an access list and the `chmod -N` that clears it, or another owner,
/// and `InvalidInput` for anything but a regular file (a directory, a FIFO). Each
/// message starts with `path`.
pub fn check_private(path: impl AsRef<Path>) -> std::io::Result<()> {
    open_private(path.as_ref(), astream_sys::Links::Follow).map(drop)
}

/// The bytes of the judged `file`, exactly as stored; a read error leads with `path`,
/// and the bytes read before it are zeroed.
fn read_judged(path: &Path, mut file: std::fs::File) -> std::io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    read_secret_file_into(&mut file, &mut bytes).map_err(|e| at_path(path, e))?;
    Ok(bytes)
}

/// A file that is [`check_private`], returned EXACTLY as stored, with no length
/// floor: the reader for an owner-only file whose content its caller decodes, such
/// as `asb serve`'s hex `--key-file`. The rule is held on the descriptor the bytes
/// are read from (the rules are the module's). Bytes accumulated before a read
/// error are zeroed before they are dropped.
///
/// # Errors
///
/// [`check_private`]'s, and any read error with its own kind. Each message starts
/// with `path`.
pub fn read_private_file(path: impl AsRef<Path>) -> std::io::Result<Vec<u8>> {
    let path = path.as_ref();
    let (file, _meta) = open_private(path, astream_sys::Links::Follow)?;
    read_judged(path, file)
}

/// THE OWNER-ONLY RING READER: the ring at `path`, [`parse_text`] over the bytes of one open
/// file held to the owner-only rule (the rules are the module's), with no link followed at the
/// path. It is [`read_file`] for a face that holds its rings private: a cap is authority, and
/// such a face wants a ring others can read, one behind a link or a FIFO refused at once.
///
/// The FILE is what it judges. A secret's other clauses do not reach a ring: its directory is
/// its keeper's choice, a second name cannot widen the mode the one file carries, and its lines
/// rather than its length say whether it is whole, so an empty ring reads as an empty ring.
///
/// # Errors
///
/// [`check_private`]'s, with `PermissionDenied` for a symlink too; any read error with its own
/// kind; and `InvalidData` for bytes that are not UTF-8 or a line that breaks a rule, naming
/// `path:line`. Each message starts with `path`. [`refusal_of`] reads the clause of a refusal.
pub fn read_private_ring(path: impl AsRef<Path>) -> std::io::Result<Vec<Line>> {
    let path = path.as_ref();
    let (file, _meta) = open_private_as(path, path, astream_sys::Links::Refuse, RING_NO_LINK)?;
    let bytes = read_judged(path, file)?;
    let text = match core::str::from_utf8(&bytes) {
        Ok(t) => t,
        Err(e) => {
            let prefix = bytes.get(..e.valid_up_to()).unwrap_or(&bytes);
            let mut line: usize = 1;
            let mut idx: usize = 0;
            while idx < prefix.len() {
                if prefix.get(idx) == Some(&b'\n') {
                    line = line.saturating_add(1);
                }
                idx = idx.saturating_add(1);
            }
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                format!("{}:{line}: {e}", path.display()),
            ));
        }
    };
    parse_text(&path.display().to_string(), text)
        .map_err(|m| std::io::Error::new(std::io::ErrorKind::InvalidData, m.to_string()))
}

/// `secret`, or `InvalidData` naming its length when it holds fewer than
/// [`SECRET_MIN`] bytes (zeroed before it is dropped).
fn at_least_min(path: &Path, mut secret: Vec<u8>) -> std::io::Result<Vec<u8>> {
    if secret.len() < SECRET_MIN {
        let held = secret.len();
        secret.fill(0);
        std::hint::black_box(&mut secret);
        return Err(std::io::Error::new(
            std::io::ErrorKind::InvalidData,
            format!(
                "{} holds {held} bytes; a secret file holds at least {SECRET_MIN} (a short \
                 key mints capabilities that seal nothing)",
                path.display()
            ),
        ));
    }
    Ok(secret)
}

/// THE SECRET FILE READER: [`read_private_file`] for a file that holds at least
/// [`SECRET_MIN`] bytes, returned EXACTLY as stored, a trailing newline included
/// (the rules are the module's). A symlink at `path` is followed: the path is the
/// operator's to name. A secret that lives in a directory of its own is read with
/// [`read_secret_in`], which holds the directory too.
///
/// The rule is held on the open file, not on the path before it is opened, so the
/// bytes returned are the bytes of the file that was judged. Secrets refused for
/// their length and bytes accumulated before read errors are zeroed before they are
/// dropped.
///
/// # Errors
///
/// [`check_private`]'s, `InvalidData` naming the byte count when it holds fewer
/// than [`SECRET_MIN`] bytes, and any other read error with its own kind. Each
/// message starts with `path`.
pub fn read_secret_file(path: impl AsRef<Path>) -> std::io::Result<Vec<u8>> {
    let path = path.as_ref();
    at_least_min(path, read_private_file(path)?)
}

/// THE SECRET FILE READER for a secret kept in a private directory: `name`, directly
/// in `dir`, read under [`read_secret_file`]'s rule and the directory's too (the
/// rules are the module's):
///
/// * `dir` is opened without following a link and must be a directory of this
///   user's, 0700 or tighter, with no access-list entry that lets anyone else in:
///   whoever can write it can replace the secret, or link it out to where others
///   read it.
/// * `name` is one path component, and the file is opened without following a link
///   (`O_NOFOLLOW`) and must have exactly ONE link: a second name for it may sit in a
///   directory others can reach.
///
/// The directory is judged by its path and the file opened by its path beneath it:
/// the directory's own parent decides who could swap the directory between the two,
/// and that parent is not judged here.
///
/// # Errors
///
/// `NotFound` when the directory or the file is not there (no file is `NotFound`
/// whatever its directory is: the directory is judged when there is a secret in it
/// to keep); `InvalidInput` for a
/// name of more than one component, a file that is not a regular file, or a
/// directory that is no directory; `PermissionDenied` for a symlink, a second link,
/// another owner, a group/other bit or an access list, on the file or the
/// directory, naming the command that closes a mode or an access list;
/// `InvalidData` for a short secret; and any other read error with its own kind.
/// Each message starts with the secret's path, `dir` joined with `name`.
pub fn read_secret_in(dir: impl AsRef<Path>, name: &str) -> std::io::Result<Vec<u8>> {
    let dir = dir.as_ref();
    let path = dir.join(name);
    if Path::new(name).file_name() != Some(std::ffi::OsStr::new(name)) {
        return Err(refused(
            &path,
            std::io::ErrorKind::InvalidInput,
            ": a secret's name in its directory is one path component",
        ));
    }
    secret_in(dir, name.as_ref(), &path, DirMode::AsItStands)
}

/// [`read_secret_in`] over `path`'s own directory and file name, every refusal
/// starting with `path` exactly as given: the reader for a secret named by one path
/// (a `--secret-file`) that is held to the directory rule too. A bare name is read
/// in the current directory and named as given, never as `./<name>`.
///
/// # Errors
///
/// [`read_secret_in`]'s, each message starting with `path`; and `InvalidInput` for a
/// path that names no file (`/`, an empty path, one ending in `..`).
pub fn read_secret_at(path: impl AsRef<Path>) -> std::io::Result<Vec<u8>> {
    let path = path.as_ref();
    let (dir, name) = dir_and_name(path)?;
    secret_in(dir, name, path, DirMode::AsItStands)
}

/// [`read_secret_at`] as it will read once the secret's directory has been narrowed to
/// 0700: a directory refused for its mode bits ALONE passes, while every other clause
/// of the directory's (no directory, a symlink, another owner, an access-list allow
/// entry) and every clause of the file's still refuses. astream-sys judges a
/// directory's mode last ([`astream_sys::owner_private_dir`]), so a mode refusal means
/// every other clause held, and `chmod 700` is all that stands between this answer and
/// [`read_secret_at`]'s.
///
/// This is the reading of a DRY RUN whose real run narrows the directory before it
/// reads the secret (aterm's `fabric on`: its root step makes the root 0700, then its
/// secret step reads the secret in it), so the preview judges the secret the real run
/// will read rather than refusing a directory the real run will have fixed. A real read
/// never uses it: it narrows the directory first, then reads with [`read_secret_at`].
///
/// # Errors
///
/// [`read_secret_at`]'s, but for a directory's group or other mode bits.
pub fn read_secret_at_narrowed(path: impl AsRef<Path>) -> std::io::Result<Vec<u8>> {
    let path = path.as_ref();
    let (dir, name) = dir_and_name(path)?;
    secret_in(dir, name, path, DirMode::Narrowed)
}

/// `path`'s directory (`.` for a bare name) and file name, or `InvalidInput` naming
/// `path` when it names no file.
fn dir_and_name(path: &Path) -> std::io::Result<(&Path, &std::ffi::OsStr)> {
    let Some(name) = path.file_name() else {
        return Err(refused(
            path,
            std::io::ErrorKind::InvalidInput,
            ": a secret's path names no file",
        ));
    };
    let dir = match path.parent() {
        Some(dir) if !dir.as_os_str().is_empty() => dir,
        _ => Path::new("."),
    };
    Ok((dir, name))
}

/// How [`secret_in`] holds its directory's mode bits.
#[derive(Clone, Copy, PartialEq, Eq)]
enum DirMode {
    /// As they stand: a group or other bit refuses the directory.
    AsItStands,
    /// As they will stand once the caller has narrowed them to 0700
    /// ([`read_secret_at_narrowed`]).
    Narrowed,
}

/// The secret `name` in `dir`, opened at `dir` joined with `name` and named as `path`
/// in every refusal: [`read_secret_in`]'s rule, its directory's mode held as `mode`
/// says. `name` is one path component; the caller made sure of it.
fn secret_in(
    dir: &Path,
    name: &std::ffi::OsStr,
    path: &Path,
    mode: DirMode,
) -> std::io::Result<Vec<u8>> {
    let at = dir.join(name);
    let opened = match astream_sys::open_nonblocking(dir, astream_sys::Links::Refuse) {
        Ok(opened) => opened,
        Err(_) if is_link(dir) => {
            return Err(refused(
                path,
                std::io::ErrorKind::PermissionDenied,
                &format!(
                    ": its directory {} is a symlink: a secret's directory is read through \
                     no link",
                    dir.display()
                ),
            ));
        }
        Err(e) => return Err(at_path(path, e)),
    };
    // No secret is `NotFound` whatever its directory is: the directory is judged
    // when there is a secret in it to keep, so a caller that answers a missing
    // secret by making one (after making its directory private) is told the secret
    // is missing, not that a directory it has yet to fix is open. This `lstat`
    // decides only which refusal is said; the reads below decide what is read.
    match std::fs::symlink_metadata(&at) {
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => return Err(at_path(path, e)),
        _ => {}
    }
    match astream_sys::owner_private_dir(&opened).map_err(|e| at_path(path, e))? {
        Ok(_) => {}
        Err(astream_sys::NotPrivate::Mode(_)) if mode == DirMode::Narrowed => {}
        Err(why) => return Err(dir_refusal(path, dir, why)),
    }
    drop(opened);
    let (file, meta) = open_private_as(&at, path, astream_sys::Links::Refuse, SECRET_NO_LINK)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        let links = meta.nlink();
        if links != 1 {
            return Err(refused(
                path,
                std::io::ErrorKind::PermissionDenied,
                &format!(
                    " has {links} links: a secret in a private directory has exactly one (a \
                     second name for it may sit where others can read it)"
                ),
            ));
        }
    }
    #[cfg(not(unix))]
    let _ = meta;
    at_least_min(path, read_judged(path, file)?)
}

/// Keep the accumulated bytes available to wipe if a file read fails partway through.
fn read_secret_file_into(file: &mut std::fs::File, secret: &mut Vec<u8>) -> std::io::Result<()> {
    let mut buf = [0u8; 512];
    loop {
        match file.read(&mut buf) {
            Ok(0) => {
                buf.fill(0);
                std::hint::black_box(&mut buf);
                return Ok(());
            }
            Ok(n) => {
                if let Some(slice) = buf.get(..n) {
                    secret.extend_from_slice(slice);
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(error) => {
                buf.fill(0);
                std::hint::black_box(&mut buf);
                secret.fill(0);
                std::hint::black_box(&mut *secret);
                return Err(error);
            }
        }
    }
}

/// Keep the accumulated bytes available to wipe if a reader fails partway through.
#[cfg(test)]
pub(crate) fn read_secret_into(
    reader: &mut impl Read,
    secret: &mut Vec<u8>,
) -> std::io::Result<()> {
    let mut buf = [0u8; 512];
    loop {
        match reader.read(&mut buf) {
            Ok(0) => {
                buf.fill(0);
                std::hint::black_box(&mut buf);
                return Ok(());
            }
            Ok(n) => {
                if let Some(slice) = buf.get(..n) {
                    secret.extend_from_slice(slice);
                }
            }
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => {}
            Err(error) => {
                buf.fill(0);
                std::hint::black_box(&mut buf);
                secret.fill(0);
                std::hint::black_box(&mut *secret);
                return Err(error);
            }
        }
    }
}

const fn nibble(b: u8) -> Option<u8> {
    match b {
        b'0'..=b'9' => Some(b.saturating_sub(b'0')),
        b'a'..=b'f' => Some(b.saturating_sub(b'a' - 10)),
        b'A'..=b'F' => Some(b.saturating_sub(b'A' - 10)),
        _ => None,
    }
}

const fn decode_tag_byte(hi_b: u8, lo_b: u8, at: usize, at1: usize) -> Result<u8, Error> {
    let Some(hi) = nibble(hi_b) else {
        return Err(Error::TagNotHex(at));
    };
    let Some(lo) = nibble(lo_b) else {
        return Err(Error::TagNotHex(at1));
    };
    Ok(((hi & 0x0f) << 4) | (lo & 0x0f))
}

/// Decode exactly [`TAG_BYTES`] bytes from 64 ASCII hex digits. Byte-indexed, so a
/// multibyte character is a non-hex byte like any other, never a panic.
const fn decode_tag(hex: &[u8]) -> Result<[u8; TAG_BYTES], Error> {
    if hex.len() != TAG_BYTES * 2 || !capfile_tag_hex_len_valid(hex.len()) {
        return Err(Error::TagLength(hex.len()));
    }
    let mut tag = [0u8; TAG_BYTES];
    let mut i = 0usize;
    while i < TAG_BYTES {
        let idx = i & 31;
        let at = idx * 2;
        let at1 = at + 1;
        if at1 >= hex.len() {
            return Err(Error::TagLength(hex.len()));
        }
        match decode_tag_byte(hex[at], hex[at1], at, at1) {
            Ok(b) => tag[idx] = b,
            Err(e) => return Err(e),
        }
        i += 1;
    }
    Ok(tag)
}
