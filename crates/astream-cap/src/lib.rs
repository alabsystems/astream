#![forbid(unsafe_code)]
// Load-bearing: the constant-time compares are pinned by tests that call the
// private `verify_diff` / `verify_attach_diff`. If `verify` / `verify_attach`
// stopped deciding through them, they would be dead outside `cfg(test)`, and this
// makes that a build failure of `targo --unverified test -p astream-cap` (the doctest build).
#![deny(dead_code)]
//! `astream-cap` — the unforgeable capability mint: the capability/ACL half of
//! "SSH" for untrusted-network use (the doctrine's "sound, unforgeable capability
//! mint") — WHO may attach where. The confidentiality/authentication half is the
//! sibling crate `astream-aead` (an XChaCha20-Poly1305 sealed wire), deliberately
//! a separate crate so its vetted cipher dependency stays isolated: this crate
//! takes no third-party dependency at all.
//!
//! A **capability is a signed grant**. A grant is an [`astream_wire::Filter`] —
//! the subject subtree its bearer may attach/observe/drive — optionally prefixed
//! with a *mode*, a *principal* and an *expiry*:
//!
//! ```text
//! grant := [ ("rw" | "ro") { "," field } ":" ] <filter>
//! field := "p=" <principal> | "exp=" <unix-ms> | "relay"     each at most once, any order
//!   /f/F/pub/>            read-write, unbound, never expires (the bare-filter form)
//!   ro:/f/F/fleet/>       read-only: subscribe/fetch, never publish or commit
//!   rw,p=n-a1b2c3d4:/f/F/in/*/*/n-a1b2c3d4/*
//!                         read-write, and only as producer_id_of("n-a1b2c3d4")
//!   rw,exp=1700000000000:/f/lab/>
//!                         read-write until that instant, and nothing from it on
//!   rw,relay,p=n-a1b2c3d4:/m/>
//!                         only carry other nodes' records, each under its origin's id
//! ```
//!
//! The prefix is unambiguous *because* [`Filter::new`] rejects any string without
//! a leading `/`: a prefixed grant can never parse as a filter, and a filter can
//! never carry a prefix. The broker holds a secret key, mints a capability by
//! tagging the **whole grant string** with HMAC-SHA256, and verifies a presented
//! capability by recomputing the tag and comparing it with a fold over all 32
//! bytes that has no early exit on the first differing one — so the mode and the
//! principal are exactly as unforgeable as the filter, and a bare filter still
//! mints and verifies over byte-for-byte the same message it always did.
//!
//! The **producer id** is derived by the broker from the principal the grant names
//! ([`producer_id_of`]), never chosen by a bearer. [`grants_publish`] refuses a
//! publish whose `producer_id` a bound grant does not derive, which is what closes
//! dedup-key poisoning: a co-permitted publisher pre-publishing a peer's next
//! `(producer_id, producer_seq)` so the peer's genuine record silently dedups away
//! to the attacker's offset.
//!
//! [`attach_proof`] / [`verify_attach`] are the proof of possession that keeps the
//! tag off the wire: the client answers a broker-chosen per-connection nonce with
//! `HMAC-SHA256(tag, nonce ‖ grant)`, so the tag is never readable out of a stream
//! and a captured attach cannot be replayed onto another connection.
//!
//! [`capfile`] is the one format a capability is STORED in — the `<grant> <tag-hex>`
//! line `asb mint` prints and every `--cap-file` reads — and the one reader for it,
//! so a face that presents a ring reads it by these rules instead of its own.
//!
//! Crypto honesty: the MAC is **HMAC-SHA256 per RFC 2104** — a standard
//! construction, not an invented MAC — and it is not this crate's:
//! `astream-digest` owns the workspace's one HMAC (`hmac_sha256_parts`, the const
//! core this crate wrote and gave it) over its own SHA-256 after FIPS 180-4, each
//! compression round checkable against the standard, pinned to the FIPS vectors, and
//! held byte-for-byte to the `sha2` crate it replaced over every length 0..=1024. The
//! MAC is pinned there to all seven RFC 4231 cases; the tags, attach proof and producer
//! ids this crate answered over `sha2` are pinned here as recorded answers. No cipher is built
//! here: encrypting the wire is
//! `astream-aead`'s job (ring's ChaCha20-Poly1305 under an in-crate HChaCha20
//! subkey: XChaCha20-Poly1305), wired into the broker
//! as `serve_tcp_sealed`; a guarded broker (`open_guarded`) composes the two.

// A contracted fn is written once, through `contract_fn!`: under a Trust compiler
// (`cfg(clean_islands)`, build.rs) it carries its `ensures` clause, which no stock rustc can
// parse, and every other compiler gets the plain fn.
#[macro_use]
#[path = "../../astream-wire/contract_fn.rs"]
mod contract_fn;

// Plain-Rust twins of the functions this crate's Clean islands compile, for a compiler
// that cannot lex the islands.
#[cfg(any(test, not(clean_islands)))]
mod twins;

pub mod capfile;
#[cfg(test)]
mod capfile_tests;
pub mod ceiling;
pub use ceiling::{
    ceiling_mode_subsumes, ceiling_mode_subsumes_code, ceiling_rule_index_clamp,
    ceiling_rule_within_cap, CeilingViolation, CeilingViolationKind, GrantCeiling,
    MAX_CEILING_RULES, MAX_RING_CAPS,
};

use astream_digest::{hmac_sha256_parts, Sha256};
use astream_wire::{Filter, Subject};

const TAG: usize = 32; // SHA-256 output size

/// Domain separator for producer-id derivation, so the id of a principal is never
/// some other SHA-256 this workspace already computes over the same bytes.
const PID_DOMAIN: &[u8] = b"astream-pid\0";

/// Offline Macaroon v2 tag context, following [`MACAROON_FRAME_PREFIX`].
const MACAROON_DOMAIN: &[u8] = b"astream-macaroon-v2\0";
/// Binary context framing disjoint from the attach message `nonce[32] ‖ grant`:
/// at byte 32 this message has 0xff, which no UTF-8 `grant` can contain. This is
/// independent of the nonce's value, including a maliciously chosen challenge.
const MACAROON_FRAME_PREFIX: [u8; 33] = [0xff; 33];

/// Maximum number of offline Macaroon attenuation hops (`via=<hex>`) in a grant.
pub const MAX_MACAROON_DEPTH: usize = 8;

/// Maximum byte length of a `via=<hex>` field in a grant prefix.
const MAX_VIA_HEX_LEN: usize = 4096;
/// Shared issuance/verification bound for a full offline chained grant. This
/// keeps pre-proof parent parsing bounded without issuing a cap it cannot verify.
const MAX_MACAROON_GRANT_BYTES: usize = MAX_VIA_HEX_LEN + 512;

/// The longest a principal's name half may be — short enough that a principal
/// cannot carry a sentence into an agent's context.
const PRINCIPAL_NAME_MAX: usize = 32;
/// Maximum byte length of a full `<class>-<name>` principal (`2 + PRINCIPAL_NAME_MAX`).
const PRINCIPAL_TOTAL_MAX: usize = 34;

/// The class prefixes a principal may carry: session, node, human, agent/service.
/// Reserved literal subject segments can never collide with a class-prefixed id.
const PRINCIPAL_CLASSES: [&str; 4] = ["s-", "n-", "h-", "a-"];

/// A bearer capability: the granted **grant string** plus its HMAC tag.
///
/// Its `Debug` output names the grant but redacts the tag: the tag IS the bearer
/// secret, and debug output ends up in logs.
#[derive(Clone, PartialEq, Eq)]
pub struct Capability {
    /// The grant this capability seals — a bare `astream_wire` filter string (the
    /// read-write, unbound grant) or a mode/principal-prefixed one ([`Grant`]).
    /// The field keeps its name because a bare filter *is* a grant.
    pub filter: String,
    /// HMAC-SHA256(secret, grant) (or chained Macaroon HMAC for `via=` grants) —
    /// the unforgeable seal, over mode, principal, expiry, provenance, and filter.
    pub tag: [u8; TAG],
}

impl std::fmt::Debug for Capability {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Capability")
            .field("filter", &self.filter)
            .field("tag", &"<redacted>")
            .finish()
    }
}

/// What a grant authorizes: reads only, or reads and writes.
///
/// `ReadOnly` covers `Subscribe`/`Last`/`Fetch`; `ReadWrite` additionally covers
/// `Publish`, `Commit` and `Will`. A read grant is never *implied* to be a write
/// grant — the two are separate capabilities on one connection's ring, which is
/// how a member reads a broadcast subtree it must not be able to write.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// Read (subscribe/fetch/last) only — never publish, commit or leave a will.
    ReadOnly,
    /// Read and write.
    ReadWrite,
}

/// A parsed grant: the mode, the optional bound principal, and the filter half.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Grant {
    /// Whether this grant may write, or only read.
    pub mode: Mode,
    /// The principal this grant binds writes to, if any. `None` is an *unbound*
    /// grant: it may publish under any producer id, so it is the god cap and the
    /// shape the fleet root keeps.
    pub principal: Option<String>,
    /// The `astream_wire` filter half — the subject subtree itself.
    pub filter: String,
    /// The instant this grant STOPS authorizing, as unix milliseconds, or `None`
    /// for a capability that never expires.
    ///
    /// It rides inside the grant STRING, which is the whole of what the tag is
    /// computed over, so like the mode and the principal it cannot be stripped,
    /// shortened or extended: any edit changes the string and the tag no longer
    /// verifies.
    ///
    /// `None` is a grant with no `exp=` field — every grant minted before the
    /// field existed, and the deliberate shape for a fleet root an operator
    /// rotates by changing the secret.
    pub expires_at: Option<u64>,
    /// A RELAY grant (`relay`): it authorizes the broker's `Relay` verb and no other write. Its
    /// bearer carries records under their origin's producer id, and only where a subject's
    /// owner segment names that origin ([`relay_owner`], [`grants_relay`]). Any `p=` names who
    /// carries them, never whose they are.
    pub relay: bool,
}

impl Grant {
    /// Parse a grant string, or explain why it is not one.
    ///
    /// A bare filter (leading `/`) is the read-write, unbound grant, which keeps
    /// capabilities minted as bare filters valid. Otherwise the string is
    /// `<mode>[,<field>]*:<filter>`, split on the FIRST `:` — unambiguous because
    /// no field value may contain one, and a filter that does is only ever
    /// reached after the prefix has been consumed.
    ///
    /// The fields are `p=<principal>`, `exp=<unix-ms>`, `relay`, and `via=<hex-parent-grant>`
    /// (for offline-attenuated Macaroon capabilities), each at most once and in any
    /// order. A REPEATED field is refused rather than last-wins: two `exp=` values
    /// in one string is not a grant whose meaning anyone should have to guess, and
    /// last-wins would let a longer expiry be appended to a string a reader skims.
    /// An UNKNOWN field is refused too, because a future field silently ignored by
    /// an older broker is a capability that means less than it says.
    pub fn parse(grant: &str) -> Result<Self, String> {
        match parse_grant(grant) {
            Ok((g, _)) => Ok(g),
            Err(e) => Err(e),
        }
    }
}

/// [`Grant::parse`], also handing back the validated filter half, so an
/// authorization check matches against it instead of validating the same
/// string a second time.
fn parse_grant(grant: &str) -> Result<(Grant, Filter), String> {
    match parse_grant_depth(grant, 0) {
        Ok((g, f, _)) => Ok((g, f)),
        Err(e) => Err(e),
    }
}

const fn all_ascii_digits(s: &str) -> bool {
    let mut bytes = s.as_bytes();
    if bytes.is_empty() {
        return false;
    }
    while let &[b, ref rest @ ..] = bytes {
        if b < b'0' || b > b'9' {
            return false;
        }
        bytes = rest;
    }
    true
}

const fn parse_u64_ascii(s: &str) -> Option<u64> {
    let mut bytes = s.as_bytes();
    if bytes.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    while let &[b, ref rest @ ..] = bytes {
        let digit = match b {
            b'0'..=b'9' => (b - b'0') as u64,
            _ => return None,
        };
        let Some(mul) = acc.checked_mul(10) else {
            return None;
        };
        let Some(next) = mul.checked_add(digit) else {
            return None;
        };
        acc = next;
        bytes = rest;
    }
    Some(acc)
}

fn parse_single_grant(
    grant: &str,
    depth: usize,
) -> Result<(Grant, Filter, Option<String>), String> {
    const MAX_MACAROON_DEPTH_LIMIT: u64 = (MAX_MACAROON_DEPTH as u64) + 1;
    if !macaroon_depth_valid(depth as u64, MAX_MACAROON_DEPTH_LIMIT) {
        return Err(format!(
            "invalid grant: macaroon attenuation chain exceeds max depth {MAX_MACAROON_DEPTH}"
        ));
    }
    if grant.starts_with('/') {
        let f = match Filter::new(grant) {
            Ok(f) => f,
            Err(e) => return Err(format!("invalid filter: {e}")),
        };
        let g = Grant {
            mode: Mode::ReadWrite,
            principal: None,
            filter: grant.to_string(),
            expires_at: None,
            relay: false,
        };
        return Ok((g, f, None));
    }
    let Some((prefix, filter)) = grant.split_once(':') else {
        return Err(format!(
            "invalid grant {grant:?}: neither a filter (leading '/') nor a \
             \"<rw|ro>[,p=<principal>]:<filter>\" prefix"
        ));
    };
    let mut fields = prefix.split(',');
    let mode_tok = fields.next().unwrap_or("");
    let mut principal: Option<String> = None;
    let mut expires_at: Option<u64> = None;
    let mut via_parent: Option<String> = None;
    let mut relay = false;
    for field in fields {
        if field == "relay" {
            if relay {
                return Err(format!(
                    "invalid grant prefix {prefix:?}: repeated \"relay\""
                ));
            }
            relay = true;
        } else if let Some(p) = field.strip_prefix("p=") {
            if principal.is_some() {
                return Err(format!("invalid grant prefix {prefix:?}: repeated \"p=\""));
            }
            if !valid_principal(p) {
                return Err(format!(
                    "invalid principal {p:?}: expected a tab ID (t and 10 base32 characters) \
                     or one of {PRINCIPAL_CLASSES:?} then 1..={PRINCIPAL_NAME_MAX} of [a-z0-9-]"
                ));
            }
            principal = Some(p.to_string());
        } else if let Some(v) = field.strip_prefix("exp=") {
            if expires_at.is_some() {
                return Err(format!(
                    "invalid grant prefix {prefix:?}: repeated \"exp=\""
                ));
            }
            // ASCII digits only, then parse: `u64::from_str` would also accept a
            // leading `+`. (Leading zeros still parse, as does either field
            // order, so one authority can have several spellings and tags;
            // nothing keys authority on the spelling.)
            if !all_ascii_digits(v) {
                return Err(format!(
                    "invalid grant expiry {v:?}: expected unix milliseconds as ASCII digits"
                ));
            }
            let Some(ms) = parse_u64_ascii(v) else {
                return Err(format!(
                    "invalid grant expiry {v:?}: does not fit in u64 milliseconds"
                ));
            };
            expires_at = Some(ms);
        } else if let Some(h) = field.strip_prefix("via=") {
            if via_parent.is_some() {
                return Err(format!(
                    "invalid grant prefix {prefix:?}: repeated \"via=\""
                ));
            }
            if !macaroon_depth_valid(depth as u64, MAX_MACAROON_DEPTH as u64) {
                return Err(format!(
                    "invalid grant: macaroon attenuation chain exceeds max depth {MAX_MACAROON_DEPTH}"
                ));
            }
            let Some(parent_str) = decode_lower_hex_utf8(h) else {
                return Err(format!(
                    "invalid grant via field {h:?}: expected lowercase hex-encoded parent grant"
                ));
            };
            via_parent = Some(parent_str);
        } else {
            return Err(format!(
                "invalid grant prefix {prefix:?}: expected \",p=<principal>\", \
                 \",exp=<unix-ms>\", \",relay\", or \",via=<hex>\""
            ));
        }
    }
    let mode = match mode_tok {
        "rw" => Mode::ReadWrite,
        "ro" => Mode::ReadOnly,
        other => {
            return Err(format!(
                "invalid grant mode {other:?}: expected \"rw\" or \"ro\""
            ))
        }
    };
    if relay && mode != Mode::ReadWrite {
        return Err(format!(
            "invalid grant prefix {prefix:?}: \"relay\" writes, so it needs \"rw\""
        ));
    }
    let f = match Filter::new(filter) {
        Ok(f) => f,
        Err(e) => return Err(format!("invalid filter: {e}")),
    };
    let g = Grant {
        mode,
        principal,
        filter: filter.to_string(),
        expires_at,
        relay,
    };
    Ok((g, f, via_parent))
}

fn parse_grant_depth(
    grant: &str,
    start_depth: usize,
) -> Result<(Grant, Filter, Option<String>), String> {
    let (root_g, root_f, root_via) = parse_single_grant(grant, start_depth)?;
    let mut child_str = grant.to_string();
    let mut child_g = root_g.clone();
    let mut child_f = root_f.clone();
    let mut next_via = root_via.clone();
    let mut cur_depth = start_depth;
    for _ in 0..=MAX_MACAROON_DEPTH {
        let Some(parent_str) = next_via else {
            return Ok((root_g, root_f, root_via));
        };
        cur_depth = cur_depth.saturating_add(1);
        let (pg, pf, p_via) = parse_single_grant(&parent_str, cur_depth)?;
        check_attenuation_parsed(&parent_str, &pg, &pf, &child_str, &child_g, &child_f)?;
        child_str = parent_str;
        child_g = pg;
        child_f = pf;
        next_via = p_via;
    }
    Err(format!(
        "invalid grant: macaroon attenuation chain exceeds max depth {MAX_MACAROON_DEPTH}"
    ))
}

const fn hex_digit_char(nibble: u8) -> char {
    match nibble & 0x0f {
        0 => '0',
        1 => '1',
        2 => '2',
        3 => '3',
        4 => '4',
        5 => '5',
        6 => '6',
        7 => '7',
        8 => '8',
        9 => '9',
        10 => 'a',
        11 => 'b',
        12 => 'c',
        13 => 'd',
        14 => 'e',
        _ => 'f',
    }
}

const fn hex_nibble(b: u8) -> Option<u8> {
    match b {
        b'0' => Some(0),
        b'1' => Some(1),
        b'2' => Some(2),
        b'3' => Some(3),
        b'4' => Some(4),
        b'5' => Some(5),
        b'6' => Some(6),
        b'7' => Some(7),
        b'8' => Some(8),
        b'9' => Some(9),
        b'a' => Some(10),
        b'b' => Some(11),
        b'c' => Some(12),
        b'd' => Some(13),
        b'e' => Some(14),
        b'f' => Some(15),
        _ => None,
    }
}

const fn encode_hex_pair(b: u8) -> (char, char) {
    (hex_digit_char(b >> 4), hex_digit_char(b & 0x0f))
}

const fn decode_hex_pair(hi_b: u8, lo_b: u8) -> Option<u8> {
    let Some(hi) = hex_nibble(hi_b) else {
        return None;
    };
    let Some(lo) = hex_nibble(lo_b) else {
        return None;
    };
    Some(((hi & 0x0f) << 4) | (lo & 0x0f))
}

fn encode_lower_hex(bytes: &[u8]) -> String {
    let mut out = String::new();
    for &b in bytes {
        let (hi, lo) = encode_hex_pair(b);
        out.push(hi);
        out.push(lo);
    }
    out
}

fn decode_lower_hex_utf8(hex: &str) -> Option<String> {
    if hex.is_empty() || hex.len() > MAX_VIA_HEX_LEN {
        return None;
    }
    let (pairs, rem) = hex.as_bytes().as_chunks::<2>();
    if !rem.is_empty() {
        return None;
    }
    let mut out = Vec::new();
    for &[hi_b, lo_b] in pairs {
        out.push(decode_hex_pair(hi_b, lo_b)?);
    }
    match core::str::from_utf8(&out) {
        Ok(s) => Some(s.to_owned()),
        Err(_) => None,
    }
}

/// The bytes of an aterm tab ID: `t` and 10 lower-case Crockford base32 characters.
const TAB_ID_LEN: usize = 11;

/// Whether `p` is an aterm tab ID: `t` and 10 characters of `0-9` and `a-z` without `i`, `l`,
/// `o` and `u` (aterm's `aterm_types::tab_id`). A session's principal is its tab ID. No
/// reserved literal subject segment is one: each is shorter than 11 bytes or holds an `i`,
/// `l`, `o` or `u`.
const fn is_tab_id(p: &[u8]) -> bool {
    if p.len() != TAB_ID_LEN {
        return false;
    }
    let &[b't', ref rest @ ..] = p else {
        return false;
    };
    let mut rest = rest;
    while let &[b, ref tail @ ..] = rest {
        if !(matches!(b, b'0'..=b'9' | b'a'..=b'h' | b'j' | b'k' | b'm' | b'n' | b'p'..=b't')
            || matches!(b, b'v'..=b'z'))
        {
            return false;
        }
        rest = tail;
    }
    true
}

const fn is_principal_body_byte(b: u8) -> bool {
    (b >= b'a' && b <= b'z') || (b >= b'0' && b <= b'9') || b == b'-'
}

/// Whether `p` is a well-formed principal: an aterm tab ID ([`is_tab_id`]), or a class prefix
/// (`s-` session, `n-` node, `h-` human, `a-` service) then `[a-z0-9-]{1,32}`.
///
/// HONEST BOUNDARY: the per-class *shape* of the name (`n-<16 hex>`) is deliberately not
/// enforced here. What this rejects is anything that could confuse the grant grammar or the
/// subject grammar — a `:`, a `/`, a wildcard, a control byte, an over-long or empty name — not
/// anything about who issued the id.
const fn valid_principal(p: &str) -> bool {
    if is_tab_id(p.as_bytes()) {
        return true;
    }
    let bytes = p.as_bytes();
    if bytes.len() > PRINCIPAL_TOTAL_MAX {
        return false;
    }
    let &[class, b'-', first, ref tail @ ..] = bytes else {
        return false;
    };
    if !matches!(class, b's' | b'n' | b'h' | b'a') {
        return false;
    }
    if !is_principal_body_byte(first) {
        return false;
    }
    let mut rest = tail;
    while let &[b, ref tail @ ..] = rest {
        if !is_principal_body_byte(b) {
            return false;
        }
        rest = tail;
    }
    true
}

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
mod cap_island;
#[cfg(not(clean_islands))]
pub use crate::twins::{attenuate_expiry_min, cap_clock_advance_monotone, live_expiry_or_zero};
#[cfg(clean_islands)]
pub use cap_island::{attenuate_expiry_min, cap_clock_advance_monotone, live_expiry_or_zero};

contract_fn! {
    /// Kernel-certified half-open expiry predicate (`exp <= now_ms`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `grant_expired_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn grant_expired_at(exp: u64, now_ms: u64) -> bool
    clauses [ensures result == (exp <= now_ms)]
    {
        exp <= now_ms
    }
}

contract_fn! {
    /// Kernel-certified principal-to-`producer_id` binding equality check.
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `pid_matches_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn producer_id_matches(expected: u64, actual: u64) -> bool
    clauses [ensures result == (expected == actual)]
    {
        expected == actual
    }
}

contract_fn! {
    /// Kernel-certified expiry-attenuation predicate (`child_exp <= parent_exp`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `expiry_attenuates_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn expiry_attenuates(child_exp: u64, parent_exp: u64) -> bool
    clauses [ensures result == (child_exp <= parent_exp)]
    {
        child_exp <= parent_exp
    }
}

contract_fn! {
    /// Kernel-certified Macaroon chain depth bound check (`depth < max_depth`).
    ///
    /// Discharged in the Clean CIC kernel by definitional equality against
    /// `depth_within_limit_isl` (`clean-kernel-defeq`).
    #[must_use]
    pub const fn macaroon_depth_valid(depth: u64, max_depth: u64) -> bool
    clauses [ensures result == (depth < max_depth)]
    {
        depth < max_depth
    }
}

/// Advance an authorization clock monotonically (`max(cur_ms, sample_ms)`),
/// matching the Clean-origin `cap_clock_advance_monotone` transition.
#[must_use]
pub const fn advance_auth_clock_ms(cur_ms: u64, sample_ms: u64) -> u64 {
    if cur_ms < sample_ms {
        sample_ms
    } else {
        cur_ms
    }
}

/// Compute the tightest effective expiry timestamp (`unix_ms`) across an entire
/// offline-attenuated Macaroon delegation chain (`via=<hex>`), folding each hop's
/// `expires_at` via the Clean-origin `attenuate_expiry_min` transition.
#[must_use]
pub fn effective_expiry_ms(grant: &str) -> Option<u64> {
    let mut cur = grant.to_string();
    let mut effective: Option<u64> = None;
    for depth in 0..=MAX_MACAROON_DEPTH {
        let Ok((parsed, _, parent)) = parse_grant_depth(&cur, depth) else {
            return None;
        };
        if let Some(exp) = parsed.expires_at {
            effective = Some(match effective {
                Some(acc) => attenuate_expiry_min(acc, exp),
                None => exp,
            });
        }
        match parent {
            None => return effective,
            Some(p) => cur = p,
        }
    }
    None
}

/// 3-parameter Macaroon expiry attenuation + live clock enforcement kernel:
/// collapses to `0` (immediately expired) if `min(parent_exp, child_exp) <= now_ms`,
/// and otherwise returns `min(parent_exp, child_exp)`.
///
/// Hand-written plain Rust, not compiled from Clean: it restates
/// `TlaCapabilityProtocol::attenuate_bounded_expiry_isl`, the island's composition of the
/// 3-parameter Clean-origin [`live_expiry_or_zero`] and 2-parameter [`attenuate_expiry_min`]
/// transitions (bounded by `attenuate_bounded_expiry_le_parent`), and astream-broker's
/// `clean_tla_protocol_surface` suite holds it to that composition over a grid of boundary
/// operands.
#[must_use]
pub const fn attenuate_bounded_expiry(now_ms: u64, parent_exp: u64, child_exp: u64) -> u64 {
    let min_exp = if parent_exp < child_exp {
        parent_exp
    } else {
        child_exp
    };
    if min_exp <= now_ms {
        0
    } else {
        min_exp
    }
}

/// Compute the live clock-bounded effective expiry (`unix_ms`) across an entire
/// offline-attenuated Macaroon delegation chain at `now_ms`, folding each hop via
/// [`attenuate_bounded_expiry`] (`0` if any link has already lapsed at `now_ms`).
#[must_use]
pub fn effective_bounded_expiry_ms(grant: &str, now_ms: u64) -> Option<u64> {
    let mut cur = grant.to_string();
    let mut effective: Option<u64> = None;
    for depth in 0..=MAX_MACAROON_DEPTH {
        let Ok((parsed, _, parent)) = parse_grant_depth(&cur, depth) else {
            return None;
        };
        if let Some(exp) = parsed.expires_at {
            effective = Some(match effective {
                Some(acc) => attenuate_bounded_expiry(now_ms, acc, exp),
                None => attenuate_bounded_expiry(now_ms, exp, exp),
            });
        }
        match parent {
            None => return effective,
            Some(p) => cur = p,
        }
    }
    None
}

/// When `grant` stops authorizing, as unix milliseconds — `None` for a grant
/// that never expires, and `None` for a string that is not a grant at all.
///
/// The two `None`s are deliberately the same answer because this is a *reader*,
/// not a gate: nothing decides authority from it. [`is_expired`] is the gate, and
/// it separates them the other way (an unparseable string is expired).
#[must_use]
pub fn expires_at(grant: &str) -> Option<u64> {
    match Grant::parse(grant) {
        Ok(g) => g.expires_at,
        Err(_) => None,
    }
}

/// Whether `grant` has stopped authorizing at `now_ms` (unix milliseconds).
///
/// `exp` is the FIRST instant at which the capability is invalid, so a grant is
/// expired when `now_ms >= exp`. Half-open, like every other range in this crate,
/// and it makes "valid until midnight" spellable exactly once.
///
/// FAIL CLOSED: a string that does not parse as a grant is reported EXPIRED. It
/// cannot authorize anything anyway ([`Grant::parse`] is on every authorization
/// path), and a gate that answered "not expired" for a malformed grant would be
/// a gate that says yes to garbage.
///
/// THE CLOCK IS THE CALLER'S. Nothing here reads one: this crate is on the
/// deterministic side of astream's effect seam, where a `SystemTime::now()` would
/// make a replay depend on when it ran. The broker passes the instant it already
/// took at the connection boundary.
#[must_use]
pub fn is_expired(grant: &str, now_ms: u64) -> bool {
    match Grant::parse(grant) {
        Err(_) => true,
        Ok(g) => match g.expires_at {
            Some(exp) => grant_expired_at(exp, now_ms),
            None => false,
        },
    }
}

/// The mode `grant` authorizes, or `None` if it is not a grant at all.
#[must_use]
pub fn mode_of(grant: &str) -> Option<Mode> {
    match Grant::parse(grant) {
        Ok(g) => Some(g.mode),
        Err(_) => None,
    }
}

/// The immediate parent grant string embedded in an offline-attenuated Macaroon
/// capability (`via=<hex>`), or `None` for a root capability or unparseable string.
#[must_use]
pub fn parent_grant(grant: &str) -> Option<String> {
    match parse_grant_depth(grant, 0) {
        Ok((_, _, p)) => p,
        Err(_) => None,
    }
}

/// The number of offline Macaroon attenuation hops (`via=<hex>`) in `grant` (`0` for
/// a root capability), or `None` if `grant` does not parse.
#[must_use]
pub fn attenuation_depth(grant: &str) -> Option<usize> {
    let mut cur = grant.to_string();
    for depth in 0..=MAX_MACAROON_DEPTH {
        let Ok((_, _, parent)) = parse_grant_depth(&cur, depth) else {
            return None;
        };
        match parent {
            None => return Some(depth),
            Some(p) => cur = p,
        }
    }
    None
}

/// Decode the 64-bit little-endian producer id from the first 8 bytes of a
/// 32-byte SHA-256 digest (`SHA-256("astream-pid\0" ‖ principal)[..8]`).
#[must_use]
pub const fn decode_producer_id_bytes(digest: &[u8; TAG]) -> u64 {
    (digest[0] as u64)
        | ((digest[1] as u64) << 8)
        | ((digest[2] as u64) << 16)
        | ((digest[3] as u64) << 24)
        | ((digest[4] as u64) << 32)
        | ((digest[5] as u64) << 40)
        | ((digest[6] as u64) << 48)
        | ((digest[7] as u64) << 56)
}

/// The producer id the **broker** derives for `principal`:
/// `u64::from_le_bytes(SHA-256("astream-pid\0" ‖ principal)[..8])`.
///
/// Nothing a bearer types is ever a producer id — a bound grant's publish must
/// carry exactly this. 64 bits is the wire's producer-id width, so a targeted
/// collision is a 2^64 second-preimage search; the broker's binding table
/// (`pid → principal`) is the belt-and-braces on top of that, not this function.
#[must_use]
pub const fn producer_id_of(principal: &str) -> u64 {
    let mut h = Sha256::new();
    h.update_slice(PID_DOMAIN);
    h.update_slice(principal.as_bytes());
    let digest: [u8; TAG] = h.finalize();
    decode_producer_id_bytes(&digest)
}

/// HMAC-SHA256(key, msg) per RFC 2104: `astream-digest`'s one HMAC
/// ([`hmac_sha256_parts`]) over a single part.
///
/// This crate held its own copy of that core until astream-digest took it, in
/// place of astream-aead's wiping copy and beside a port of aterm-digest's
/// streaming API: four copies of the same RFC (aterm's two have since gone too),
/// which nothing held to each other. The tags, attach proofs and
/// producer ids below are still pinned here as recorded answers
/// (`tags_proofs_and_producer_ids_are_the_recorded_answers`), because they are
/// this crate's wire contract; the RFC 4231 vectors are the MAC's, and moved with
/// it.
const fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; TAG] {
    hmac_sha256_parts(key, &[msg])
}

/// The offline tag message has an explicit binary context before any grant.
///
/// Root-capability tags and the attach wire message are unchanged. Old offline
/// v1 tags are intentionally refused: reissue every offline chain from its root
/// capability. There is no legacy tag fallback, which would retain the proof
/// substitution vulnerability. The `via=` grant and capfile syntax stay unchanged.
const fn macaroon_tag(parent_tag: &[u8; TAG], grant: &str) -> [u8; TAG] {
    hmac_sha256_parts(
        parent_tag,
        &[&MACAROON_FRAME_PREFIX, MACAROON_DOMAIN, grant.as_bytes()],
    )
}

/// Compute the expected HMAC tag for `grant` under `secret`, supporting both root
/// capabilities (`HMAC-SHA256(secret, grant)`) and offline-attenuated Macaroon
/// capabilities carrying `via=<hex-parent-grant>` (`HMAC-SHA256(parent_tag, MACAROON_FRAME_PREFIX ‖ MACAROON_DOMAIN ‖ grant)`).
///
/// Fast-path allocation guard (`cap.attach-proof-before-parse`): if `grant` starts
/// with `'/'`, exceeds `MAX_MACAROON_GRANT_BYTES` bytes, or has no `,via=` in its
/// prefix, this computes `hmac_sha256(secret, grant.as_bytes())` directly with zero
/// heap allocation.
fn expected_tag(secret: &[u8], grant: &str) -> [u8; TAG] {
    expected_tag_depth(secret, grant, 0)
}

fn has_via_hop(grant: &str, depth: usize) -> bool {
    if grant.starts_with('/')
        || grant.len() > MAX_MACAROON_GRANT_BYTES
        || !macaroon_depth_valid(depth as u64, MAX_MACAROON_DEPTH as u64)
    {
        return false;
    }
    match grant.split_once(':') {
        Some((pfx, _)) => pfx.contains(",via="),
        None => false,
    }
}

fn expected_tag_depth(secret: &[u8], grant: &str, start_depth: usize) -> [u8; TAG] {
    if !has_via_hop(grant, start_depth) {
        return hmac_sha256(secret, grant.as_bytes());
    }
    let Ok((_, _, Some(first_parent))) = parse_grant_depth(grant, start_depth) else {
        return hmac_sha256(secret, grant.as_bytes());
    };
    let mut children: Vec<String> = Vec::new();
    children.push(grant.to_string());
    let mut cur = first_parent;
    let mut cur_depth = start_depth.saturating_add(1);
    for _ in 0..MAX_MACAROON_DEPTH {
        if !has_via_hop(&cur, cur_depth) {
            break;
        }
        let Ok((_, _, Some(next_parent))) = parse_grant_depth(&cur, cur_depth) else {
            break;
        };
        children.push(cur);
        cur = next_parent;
        cur_depth = cur_depth.saturating_add(1);
    }
    let mut tag = hmac_sha256(secret, cur.as_bytes());
    while let Some(child) = children.pop() {
        tag = macaroon_tag(&tag, &child);
    }
    tag
}

/// The folded difference between two tags: the OR of all 32 byte-wise XORs. Zero
/// exactly when they are equal.
///
/// The expression has no data-dependent exit — every one of the 32 bytes is read and
/// folded whatever the inputs are, so how long the compare runs, and what it
/// returns, say nothing about WHERE the first difference is.
///
/// This is pinned on the path the security check takes: [`verify`] and
/// [`verify_attach`] each decide by testing `verify_diff` / `verify_attach_diff`
/// against zero, and the tests assert, for every ordered pair of mismatch
/// positions, that those helpers carry the LATER byte's difference as well as the
/// earlier one. A rewrite to `a == b` or to an early-exit loop fails those tests;
/// one that compares in the entry point instead leaves the helper uncalled, which
/// `deny(dead_code)` makes a build failure. It is a structural property of the
/// source, not a timing measurement.
const fn ct_diff(a: &[u8; TAG], b: &[u8; TAG]) -> u8 {
    (a[0] ^ b[0])
        | (a[1] ^ b[1])
        | (a[2] ^ b[2])
        | (a[3] ^ b[3])
        | (a[4] ^ b[4])
        | (a[5] ^ b[5])
        | (a[6] ^ b[6])
        | (a[7] ^ b[7])
        | (a[8] ^ b[8])
        | (a[9] ^ b[9])
        | (a[10] ^ b[10])
        | (a[11] ^ b[11])
        | (a[12] ^ b[12])
        | (a[13] ^ b[13])
        | (a[14] ^ b[14])
        | (a[15] ^ b[15])
        | (a[16] ^ b[16])
        | (a[17] ^ b[17])
        | (a[18] ^ b[18])
        | (a[19] ^ b[19])
        | (a[20] ^ b[20])
        | (a[21] ^ b[21])
        | (a[22] ^ b[22])
        | (a[23] ^ b[23])
        | (a[24] ^ b[24])
        | (a[25] ^ b[25])
        | (a[26] ^ b[26])
        | (a[27] ^ b[27])
        | (a[28] ^ b[28])
        | (a[29] ^ b[29])
        | (a[30] ^ b[30])
        | (a[31] ^ b[31])
}

/// Mint a capability granting `grant`, sealed with `secret`. The grant is parsed —
/// its filter half validated by `Filter::new` — so an unparseable grant (a bad
/// mode, a malformed principal, an invalid filter) is rejected up front. The tag
/// is over the grant string exactly as given (including Macaroon HMAC chain
/// derivation when `grant` carries a valid `via=<hex>` parent).
pub fn mint(secret: &[u8], grant: &str) -> Result<Capability, String> {
    Grant::parse(grant)?;
    Ok(Capability {
        filter: grant.to_string(),
        tag: expected_tag(secret, grant),
    })
}

/// The fold [`verify`] decides on: [`ct_diff`] between the tag `secret` would have
/// minted for this capability's grant and the tag the capability carries. Zero
/// exactly when the capability is genuine.
///
/// It exists so the no-early-exit shape can be asserted *through the function the
/// mint check calls* rather than beside it — see `ct_diff`.
fn verify_diff(secret: &[u8], cap: &Capability) -> u8 {
    ct_diff(&expected_tag(secret, &cap.filter), &cap.tag)
}

/// Verify a capability was minted with `secret` — its grant string (mode,
/// principal and filter alike) has not been tampered with. The tag compare folds
/// all 32 bytes, with no early exit on the first differing byte.
pub fn verify(secret: &[u8], cap: &Capability) -> bool {
    verify_diff(secret, cap) == 0
}

/// The proof of possession a client sends *instead of* its tag:
/// `HMAC-SHA256(tag, nonce ‖ grant)` over the broker's per-connection nonce.
///
/// The tag never leaves the client, and the proof is bound to both the nonce (so a
/// captured `Attach` frame replayed on a second connection is refused) and the
/// grant (so a proof for one grant cannot be presented for another).
#[must_use]
pub const fn attach_proof(tag: &[u8; TAG], nonce: &[u8], grant: &str) -> [u8; TAG] {
    hmac_sha256_parts(tag, &[nonce, grant.as_bytes()])
}

/// The fold [`verify_attach`] decides on: [`ct_diff`] between the proof `secret`
/// would have expected for `grant` over `nonce` and the proof presented. `None`
/// for a proof that is not `TAG` bytes long, refused on the length alone (which
/// the wire has already revealed; never a panic), and for a genuine proof over a
/// string that is not a grant, so no MAC is trusted for it.
///
/// The grant is parsed only once the proof has matched. It arrives from a peer
/// that has proved nothing yet, and parsing builds a [`Filter`] costing tens of
/// bytes per segment, so parsing first would let any peer make the broker
/// allocate ~36x a frame-sized grant; hashing it costs one copy.
///
/// It exists so the no-early-exit shape can be asserted *through the function the
/// accept path calls* rather than beside it — see `ct_diff`.
const fn proof_array(proof: &[u8]) -> Option<[u8; TAG]> {
    let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31] =
        proof
    else {
        return None;
    };
    Some([
        b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19,
        b20, b21, b22, b23, b24, b25, b26, b27, b28, b29, b30, b31,
    ])
}

fn verify_attach_diff(secret: &[u8], grant: &str, nonce: &[u8], proof: &[u8]) -> Option<u8> {
    let proof = proof_array(proof)?;
    let tag = expected_tag(secret, grant);
    let diff = ct_diff(&attach_proof(&tag, nonce, grant), &proof);
    if diff == 0 && Grant::parse(grant).is_err() {
        return None;
    }
    Some(diff)
}

/// The broker side of the proof of possession: recompute the tag `secret` would
/// have minted for `grant`, recompute the expected proof over `nonce`, and compare
/// the two with `verify_attach_diff` — all 32 bytes folded, no early exit on the
/// first differing byte, a wrong length an ordinary mismatch.
///
/// A string that is not a grant authorizes nothing, even under a genuine proof.
/// It is parsed only after the proof has matched, so a peer without one never
/// gets its grant string parsed at all.
#[must_use]
pub fn verify_attach(secret: &[u8], grant: &str, nonce: &[u8], proof: &[u8]) -> bool {
    verify_attach_diff(secret, grant, nonce, proof) == Some(0)
}

/// The parsed grant, and its validated filter, of a capability that is genuine
/// under `secret` AND has not expired at `now_ms`, or `None`.
///
/// THE ONE PLACE EXPIRY IS DECIDED. Every public predicate in this crate reaches
/// authority through here or through [`rw_matches`], which itself starts here, so
/// an expired capability cannot authorize a read, a write, a publish, a commit or
/// a subscribe — and a future predicate cannot forget the check, because there is
/// no other way in.
fn authentic_grant(secret: &[u8], cap: &Capability, now_ms: u64) -> Option<(Grant, Filter)> {
    if !verify(secret, cap) {
        return None;
    }
    let Ok((grant, filter)) = parse_grant(cap.filter.as_str()) else {
        return None;
    };
    match grant.expires_at {
        Some(exp) if grant_expired_at(exp, now_ms) => None,
        _ => Some((grant, filter)),
    }
}

/// The genuine, read-write grant of `cap` whose filter matches `subject`, if any.
/// The one place the write half of the §8.2 matrix is decided.
fn rw_matches(secret: &[u8], cap: &Capability, subject: &str, now_ms: u64) -> Option<Grant> {
    let (grant, filter) = authentic_grant(secret, cap, now_ms)?;
    // A relay grant writes through [`grants_relay`] alone: not a publish, a commit or a will.
    if grant.mode != Mode::ReadWrite || grant.relay {
        return None;
    }
    match Subject::new(subject) {
        Ok(s) if filter.matches(&s) => Some(grant),
        _ => None,
    }
}

/// The node that owns `subject`: the segment that says whose record it is, on the subject shapes
/// that replicate between machines. `None` for every other subject, which no relay carries:
///
/// ```text
/// /t/<table>/<n-node>[/…]             a node's rows of a table
/// /m/<n-node>[/…]                     a node's metrics
/// /f/<fleet>/pub/<n-node>[/…]         a node's presence and its sessions' topics
/// /f/<fleet>/cur/<n-node>[/…]         a node's cursors
/// /f/<fleet>/halt/<n-node>[/…]        a node's halts
/// /f/<fleet>/in/<class>/<to>/<n-node>/<kind>   mail, owned by its sender
/// ```
///
/// An owner is a node because a relayed record is signed by its node's key, whose
/// `identity_principal` is this segment. A person has no such key, so a person's subjects travel
/// under a node's, or by a mirror.
#[must_use]
pub fn relay_owner(subject: &str) -> Option<&str> {
    let mut segs = subject.strip_prefix('/')?.split('/');
    let owner = match segs.next()? {
        "t" => {
            segs.next()?;
            segs.next()?
        }
        "m" => segs.next()?,
        "f" => {
            segs.next()?;
            match segs.next()? {
                "pub" | "cur" | "halt" => segs.next()?,
                "in" => {
                    segs.next()?;
                    segs.next()?;
                    let src = segs.next()?;
                    segs.next()?;
                    if segs.next().is_some() {
                        return None;
                    }
                    src
                }
                _ => return None,
            }
        }
        _ => return None,
    };
    if owner.starts_with("n-") && valid_principal(owner) {
        Some(owner)
    } else {
        None
    }
}

/// The producer id a record of `subject` must carry to be relayed: its owner's
/// ([`relay_owner`]).
#[must_use]
pub fn relay_producer_of(subject: &str) -> Option<u64> {
    relay_owner(subject).map(producer_id_of)
}

/// Whether `cap` authorizes carrying a record of `subject` under `producer_id`: it is genuine,
/// read-write, a relay grant or unbound (the god cap holds every write), its filter matches the
/// subject, and the id is the subject's owner's ([`relay_producer_of`]). So a relay can write
/// under an origin's id only where a subject names that origin. It is an authorization of the
/// carrier, not a proof of the origin: the broker also checks each record against the origin's
/// own signature before it appends it.
#[must_use]
pub fn grants_relay(
    secret: &[u8],
    cap: &Capability,
    subject: &str,
    producer_id: u64,
    now_ms: u64,
) -> bool {
    let Some((grant, filter)) = authentic_grant(secret, cap, now_ms) else {
        return false;
    };
    if grant.mode != Mode::ReadWrite || (!grant.relay && grant.principal.is_some()) {
        return false;
    }
    let Ok(s) = Subject::new(subject) else {
        return false;
    };
    filter.matches(&s)
        && match relay_producer_of(subject) {
            Some(owner_id) => producer_id_matches(owner_id, producer_id),
            None => false,
        }
}

/// Whether `cap` (verified under `secret`) authorizes `subject` for a WRITE — it is
/// genuine, read-write, and its granted filter matches the subject.
///
/// HONEST BOUNDARY: it does **not** check the producer binding, because it is not
/// given a producer id — [`grants_publish`] is the check that closes dedup-key
/// poisoning, and [`grants_commit`] is this same rule named for a group.
///
/// `now_ms` is unix milliseconds, and every predicate here takes one: an expired
/// capability authorizes nothing (see [`Grant::expires_at`]). Pass the instant the
/// caller already holds — this crate never reads a clock.
pub fn grants(secret: &[u8], cap: &Capability, subject: &str, now_ms: u64) -> bool {
    rw_matches(secret, cap, subject, now_ms).is_some()
}

/// Whether `cap` authorizes publishing to `subject` **as** `producer_id`: genuine,
/// read-write, filter matches, and — when the grant names a principal — the id is
/// exactly the one the broker derives from that principal.
///
/// An unbound grant (no principal) may publish under any id: that is the god cap
/// the fleet root keeps, and the reason a mint face should require an explicit mode.
pub fn grants_publish(
    secret: &[u8],
    cap: &Capability,
    subject: &str,
    producer_id: u64,
    now_ms: u64,
) -> bool {
    match rw_matches(secret, cap, subject, now_ms) {
        None => false,
        Some(grant) => match grant.principal {
            None => true,
            Some(p) => producer_id_matches(producer_id_of(&p), producer_id),
        },
    }
}

/// Whether `cap` authorizes committing a consumer group whose NAME is `group`:
/// genuine, read-write, and the granted filter matches that name (group names are
/// subjects the capability must grant; they are never delivered).
///
/// The producer binding does not apply — a commit carries no producer id.
pub fn grants_commit(secret: &[u8], cap: &Capability, group: &str, now_ms: u64) -> bool {
    rw_matches(secret, cap, group, now_ms).is_some()
}

/// Whether `cap` (verified under `secret`) authorizes SUBSCRIBING with `filter`
/// -- it is genuine AND its granted filter CONTAINS the requested filter (every
/// subject the request could match is inside the grant). The filter twin of
/// [`grants`]: the ACL check a broker runs before a capability-scoped subscribe.
///
/// Mode-agnostic on purpose: a read-only grant is a full *read* grant.
pub fn grants_filter(secret: &[u8], cap: &Capability, filter: &str, now_ms: u64) -> bool {
    let Some((_, granted)) = authentic_grant(secret, cap, now_ms) else {
        return false;
    };
    match Filter::new(filter) {
        Ok(requested) => granted.contains(&requested),
        Err(_) => false,
    }
}

fn check_attenuation_parsed(
    parent_grant: &str,
    pg: &Grant,
    pf: &Filter,
    child_grant: &str,
    cg: &Grant,
    cf: &Filter,
) -> Result<(), String> {
    if pg.mode == Mode::ReadOnly && cg.mode == Mode::ReadWrite {
        return Err(format!(
            "cannot attenuate mode: parent {parent_grant:?} is ReadOnly, child {child_grant:?} requests ReadWrite"
        ));
    }
    // A relay grant and an ordinary write authorize different things: a relay writes under other
    // ids, an ordinary write under one. Only an unbound parent, which may write under any id,
    // holds both, so only it may hand down a relay; a writing child of a relay stays one.
    if cg.relay && !pg.relay && pg.principal.is_some() {
        return Err(format!(
            "cannot attenuate to a relay: parent {parent_grant:?} writes only as its principal, child {child_grant:?} would write under other ids"
        ));
    }
    if pg.relay && cg.mode == Mode::ReadWrite && !cg.relay {
        return Err(format!(
            "cannot attenuate a relay: parent {parent_grant:?} carries others' records, child {child_grant:?} would publish"
        ));
    }
    if let Some(pp) = &pg.principal {
        if cg.principal.as_ref() != Some(pp) {
            return Err(format!(
                "cannot attenuate principal: parent {parent_grant:?} is bound to {pp:?}, child {child_grant:?} has {:?}",
                cg.principal
            ));
        }
    }
    if let Some(p_exp) = pg.expires_at {
        match cg.expires_at {
            Some(c_exp) if expiry_attenuates(c_exp, p_exp) => {}
            Some(c_exp) => {
                return Err(format!(
                    "cannot attenuate expiry: child expiry {c_exp} exceeds parent expiry {p_exp}"
                ))
            }
            None => {
                return Err(format!(
                    "cannot attenuate expiry: parent expires at {p_exp}, child has no expiry"
                ))
            }
        }
    }
    if !pf.contains(cf) {
        return Err(format!(
            "cannot attenuate filter: parent filter {:?} does not contain child filter {:?}",
            pg.filter, cg.filter
        ));
    }
    Ok(())
}

/// Check whether `child_grant` is a valid, monotone attenuation of `parent_grant`
/// (`REQUIREMENTS` R6):
///
/// 1. **Mode**: `child.mode <= parent.mode` (`ReadOnly <= ReadWrite`; a `ReadOnly`
///    parent can never attenuate to `ReadWrite`).
/// 2. **Principal**: If `parent.principal` is `Some(p)`, `child.principal` must also
///    be `Some(p)` (a principal-bound grant cannot unbind or switch principals). An
///    unbound parent (`None`) may remain unbound or bind any valid principal.
/// 3. **Expiry**: If `parent.expires_at` is `Some(exp_p)`, `child.expires_at` must be
///    `Some(exp_c)` with `exp_c <= exp_p` ([`expiry_attenuates`]). A non-expiring
///    parent (`None`) may remain non-expiring or add an expiry.
/// 4. **Filter**: `parent_filter.contains(&child_filter)` — every subject matched by
///    `child_grant` is matched by `parent_grant`.
/// 5. **Relay**: a relay child needs a relay or an unbound parent; a read-write child of a relay
///    is a relay. A relay may attenuate to `ReadOnly`.
pub fn can_attenuate(parent_grant: &str, child_grant: &str) -> Result<(), String> {
    let (pg, pf) = parse_grant(parent_grant)?;
    let (cg, cf) = parse_grant(child_grant)?;
    check_attenuation_parsed(parent_grant, &pg, &pf, child_grant, &cg, &cf)
}

/// Mint an attenuated child capability from a verified, non-expired `parent`
/// capability under `secret` at `now_ms` (`REQUIREMENTS` R6).
///
/// Fails closed if `parent` does not verify under `secret`, has expired at `now_ms`,
/// or if `child_grant` widens any dimension of `parent` ([`can_attenuate`]).
pub fn attenuate(
    secret: &[u8],
    parent: &Capability,
    child_grant: &str,
    now_ms: u64,
) -> Result<Capability, String> {
    if !verify(secret, parent) {
        return Err("parent capability tag does not verify under secret".to_string());
    }
    if is_expired(&parent.filter, now_ms) {
        let exp = expires_at(&parent.filter).unwrap_or(0);
        return Err(format!(
            "parent capability expired at {exp} (now {now_ms}, unix ms)"
        ));
    }
    can_attenuate(&parent.filter, child_grant)?;
    mint(secret, child_grant)
}

/// Offline bearer-attenuated Macaroon capability derivation (`ROADMAP.md` & `REQUIREMENTS` R6).
///
/// Derives a narrower child [`Capability`] from `parent` **without** the broker's
/// master `secret`:
/// - Validates that `parent` has not expired at `now_ms` and that `child_grant`
///   is a valid monotone narrowing of `parent.filter` ([`can_attenuate`]).
/// - Embeds `via=<hex(parent.filter)>` into the child grant's prefix (bounded to
///   [`MAX_MACAROON_DEPTH`] hops).
/// - Computes `tag = HMAC-SHA256(parent.tag, MACAROON_FRAME_PREFIX ‖ MACAROON_DOMAIN ‖ chained_grant)`.
///
/// Given a genuine parent, the resulting capability verifies directly under
/// [`verify`], [`verify_attach`], [`grants`], [`grants_publish`], [`grants_commit`],
/// and [`grants_filter`] on any broker holding the root `secret`.
///
/// This issues binary-framed v2 offline tags. Root-capability tags, attach proofs,
/// and the `via=` grant/capfile syntax are unchanged. Existing v1 offline chains
/// must be reissued from their roots; their old tags are deliberately not accepted.
/// An over-bound chained grant is refused before its hex encoding is allocated.
pub fn attenuate_offline(
    parent: &Capability,
    child_grant: &str,
    now_ms: u64,
) -> Result<Capability, String> {
    if is_expired(&parent.filter, now_ms) {
        let exp = expires_at(&parent.filter).unwrap_or(0);
        return Err(format!(
            "parent capability expired at {exp} (now {now_ms}, unix ms)"
        ));
    }
    let (cg, _, child_via) = parse_grant_depth(child_grant, 0)?;
    if child_via.is_some() {
        return Err(
            "child_grant passed to attenuate_offline must not already contain a via= field"
                .to_string(),
        );
    }
    can_attenuate(&parent.filter, child_grant)?;
    let mode_str = match cg.mode {
        Mode::ReadWrite => "rw",
        Mode::ReadOnly => "ro",
    };
    let mut prefix = String::from(mode_str);
    if let Some(ref p) = cg.principal {
        prefix.push_str(",p=");
        prefix.push_str(p);
    }
    if let Some(exp) = cg.expires_at {
        prefix.push_str(&format!(",exp={exp}"));
    }
    if cg.relay {
        prefix.push_str(",relay");
    }
    prefix.push_str(",via=");
    let Some(parent_hex_len) = parent.filter.len().checked_mul(2) else {
        return Err("parent grant exceeds the offline via= byte bound".to_string());
    };
    if parent_hex_len > MAX_VIA_HEX_LEN {
        return Err("parent grant exceeds the offline via= byte bound".to_string());
    }
    let Some(l1) = prefix.len().checked_add(parent_hex_len) else {
        return Err("child grant exceeds the offline chained-grant byte bound".to_string());
    };
    let Some(l2) = l1.checked_add(1) else {
        return Err("child grant exceeds the offline chained-grant byte bound".to_string());
    };
    let Some(total_len) = l2.checked_add(cg.filter.len()) else {
        return Err("child grant exceeds the offline chained-grant byte bound".to_string());
    };
    if total_len > MAX_MACAROON_GRANT_BYTES {
        return Err("child grant exceeds the offline chained-grant byte bound".to_string());
    }
    prefix.push_str(&encode_lower_hex(parent.filter.as_bytes()));
    let chained = format!("{prefix}:{}", cg.filter);
    // Validate the full chained grant (including depth and hex bounds).
    Grant::parse(&chained)?;
    let tag = macaroon_tag(&parent.tag, &chained);
    Ok(Capability {
        filter: chained,
        tag,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn offline_macaroon_attenuation_chains_verify_without_secret_at_mint_time() {
        let secret = b"0123456789abcdef0123456789abcdef";
        let root = mint(secret, "rw:/f/fleet/>").unwrap();
        assert_eq!(attenuation_depth(&root.filter), Some(0));
        assert_eq!(parent_grant(&root.filter), None);

        // Hop 1 (offline — no secret passed!): unbound root -> principal-bound + expiring node cap.
        let node_cap = attenuate_offline(
            &root,
            "rw,p=n-0123456789abcdef,exp=2000:/f/fleet/in/n-0123456789abcdef/>",
            1000,
        )
        .unwrap();
        assert_eq!(attenuation_depth(&node_cap.filter), Some(1));
        assert_eq!(
            parent_grant(&node_cap.filter).as_deref(),
            Some("rw:/f/fleet/>")
        );
        assert!(verify(secret, &node_cap));
        let nonce = [0x42u8; 32];
        let proof1 = attach_proof(&node_cap.tag, &nonce, &node_cap.filter);
        assert!(verify_attach(secret, &node_cap.filter, &nonce, &proof1));
        let pid = producer_id_of("n-0123456789abcdef");
        assert!(grants_publish(
            secret,
            &node_cap,
            "/f/fleet/in/n-0123456789abcdef/task",
            pid,
            1500,
        ));
        assert!(!grants_publish(
            secret,
            &node_cap,
            "/f/fleet/in/n-0123456789abcdef/task",
            pid,
            2000,
        ));

        // Hop 2 (offline — chained from node_cap!): rw -> ro + tighter expiry + narrower filter.
        let tool_ro = attenuate_offline(
            &node_cap,
            "ro,p=n-0123456789abcdef,exp=1500:/f/fleet/in/n-0123456789abcdef/task",
            1000,
        )
        .unwrap();
        assert_eq!(attenuation_depth(&tool_ro.filter), Some(2));
        assert!(verify(secret, &tool_ro));
        let proof2 = attach_proof(&tool_ro.tag, &nonce, &tool_ro.filter);
        assert!(verify_attach(secret, &tool_ro.filter, &nonce, &proof2));
        assert!(grants_filter(
            secret,
            &tool_ro,
            "/f/fleet/in/n-0123456789abcdef/task",
            1499,
        ));
        // Read-only cannot publish or commit:
        assert!(!grants_publish(
            secret,
            &tool_ro,
            "/f/fleet/in/n-0123456789abcdef/task",
            pid,
            1200,
        ));
        // Expired at 1500:
        assert!(!grants_filter(
            secret,
            &tool_ro,
            "/f/fleet/in/n-0123456789abcdef/task",
            1500,
        ));

        // Forgery attempt: bearer of tool_ro tries to hand-craft a widened `rw` via= grant
        // signed with `tool_ro.tag`!
        let forged_grant = format!(
            "rw,p=n-0123456789abcdef,exp=1500,via={}:/f/fleet/in/n-0123456789abcdef/task",
            encode_lower_hex(tool_ro.filter.as_bytes())
        );
        let forged_tag = macaroon_tag(&tool_ro.tag, &forged_grant);
        let forged_cap = Capability {
            filter: forged_grant.clone(),
            tag: forged_tag,
        };
        assert!(Grant::parse(&forged_grant).is_err());
        assert!(!verify(secret, &forged_cap));
        let forged_proof = attach_proof(&forged_cap.tag, &nonce, &forged_cap.filter);
        assert!(!verify_attach(
            secret,
            &forged_cap.filter,
            &nonce,
            &forged_proof
        ));
    }

    #[test]
    fn capability_attenuation_enforces_monotone_narrowing() {
        let secret = b"0123456789abcdef0123456789abcdef";
        let root = mint(secret, "rw:/f/fleet/>").unwrap();

        // 1. Narrowing unbound root -> principal-bound + expiring + narrower subtree succeeds.
        let node = attenuate(
            secret,
            &root,
            "rw,p=n-0123456789abcdef,exp=2000:/f/fleet/in/n-0123456789abcdef/>",
            1000,
        )
        .unwrap();
        assert!(verify(secret, &node));

        // 2. Narrowing rw -> ro with tighter expiry and narrower filter succeeds.
        let ro_child = attenuate(
            secret,
            &node,
            "ro,p=n-0123456789abcdef,exp=1500:/f/fleet/in/n-0123456789abcdef/task",
            1000,
        )
        .unwrap();
        assert!(verify(secret, &ro_child));

        // 3. Widening ro -> rw is refused.
        assert!(attenuate(
            secret,
            &ro_child,
            "rw,p=n-0123456789abcdef,exp=1500:/f/fleet/in/n-0123456789abcdef/task",
            1000,
        )
        .is_err());

        // 4. Widening expiry (1600 > 1500) or dropping expiry is refused.
        assert!(attenuate(
            secret,
            &ro_child,
            "ro,p=n-0123456789abcdef,exp=1600:/f/fleet/in/n-0123456789abcdef/task",
            1000,
        )
        .is_err());
        assert!(attenuate(
            secret,
            &ro_child,
            "ro,p=n-0123456789abcdef:/f/fleet/in/n-0123456789abcdef/task",
            1000,
        )
        .is_err());

        // 5. Changing or dropping principal binding is refused.
        assert!(attenuate(
            secret,
            &node,
            "rw,p=n-fedcba9876543210,exp=1500:/f/fleet/in/n-0123456789abcdef/task",
            1000,
        )
        .is_err());
        assert!(attenuate(
            secret,
            &node,
            "rw,exp=1500:/f/fleet/in/n-0123456789abcdef/task",
            1000,
        )
        .is_err());

        // 6. Widening filter is refused.
        assert!(attenuate(
            secret,
            &node,
            "rw,p=n-0123456789abcdef,exp=1500:/f/fleet/>",
            1000,
        )
        .is_err());

        // 7. Attenuating an expired parent capability is refused.
        assert!(attenuate(
            secret,
            &node,
            "ro,p=n-0123456789abcdef,exp=1500:/f/fleet/in/n-0123456789abcdef/task",
            2000,
        )
        .is_err());
    }

    #[test]
    fn debug_output_names_the_grant_but_never_the_tag() {
        let cap = mint(b"k", "/a/>").unwrap();
        assert_eq!(
            format!("{cap:?}"),
            r#"Capability { filter: "/a/>", tag: "<redacted>" }"#
        );
    }

    /// A FIXED instant for every authorization call below: this crate reads no
    /// clock, so a test that passed one would be testing the machine.
    const T0: u64 = 1_700_000_000_000;

    #[test]
    fn grants_filter_scopes_subscribe_to_the_granted_subtree() {
        let secret = b"broker-secret";
        let cap = mint(secret, "/a/stream/s1/>").unwrap();
        assert!(grants_filter(secret, &cap, "/a/stream/s1/out", T0));
        assert!(grants_filter(secret, &cap, "/a/stream/s1/>", T0));
        assert!(grants_filter(secret, &cap, "/a/stream/s1/*", T0));
        assert!(!grants_filter(secret, &cap, "/a/stream/s2/out", T0));
        assert!(!grants_filter(secret, &cap, "/a/>", T0));
        // a forged/widened cap (real tag, swapped filter) is rejected.
        let forged = Capability {
            filter: "/a/>".to_string(),
            tag: cap.tag,
        };
        assert!(!grants_filter(secret, &forged, "/a/x", T0));
    }

    /// `attach_proof` streams nonce and grant into the MAC instead of joining them
    /// first: the proof must be the HMAC of the concatenation, byte for byte —
    /// including the empty-nonce and empty-grant edges.
    #[test]
    fn attach_proof_is_the_hmac_of_nonce_then_grant() {
        let tag = [7u8; TAG];
        for (nonce, grant) in [
            (&b"\x01\x02\x03nonce"[..], "ro:/a/>"),
            (&b""[..], "ro:/a/>"),
            (&b"only-nonce"[..], ""),
            (&[0u8; 200][..], "rw:/a/b/c"),
        ] {
            let mut joined = nonce.to_vec();
            joined.extend_from_slice(grant.as_bytes());
            assert_eq!(attach_proof(&tag, nonce, grant), hmac_sha256(&tag, &joined));
        }
        // The split point is not part of the MAC: only the joined bytes are.
        assert_eq!(
            attach_proof(&tag, b"ab", "cd"),
            attach_proof(&tag, b"abc", "d")
        );
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|b| format!("{b:02x}")).collect()
    }

    /// Recorded answers: the tags, the attach proof and the producer ids below were
    /// computed by this crate over the `sha2` crate (0.10.9) on 2026-10-15, before
    /// it moved to `astream-digest`, and pass unchanged over it, and over the HMAC
    /// that moved there after it. They are the wire contract a broker and every
    /// bridge must keep agreeing on, so the hash and the MAC under them can change
    /// only if they do not. The secrets straddle the 64-byte HMAC block (shorter, exactly 64 —
    /// padded, never hashed — 65, and RFC 4231's 131); the principals put
    /// `"astream-pid\0" ‖ principal` on each side of SHA-256's 55/56-byte padding
    /// split and its 64-byte block.
    #[test]
    fn tags_proofs_and_producer_ids_are_the_recorded_answers() {
        let grants = [
            "/a/stream/>",
            "ro:/f/F/fleet/>",
            "rw,p=n-a1b2c3d4,exp=1700000000000:/f/F/in/*/*/n-a1b2c3d4/*",
        ];
        let secrets: [&[u8]; 4] = [b"broker-secret-key", &[0x5a; 64], &[0xa5; 65], &[0xaa; 131]];
        let tags: [[&str; 3]; 4] = [
            [
                "1084b08e4e2ade86386403d8b518566857c31a730cf5f206a0293204c88aa5f2",
                "d2912c76afb62dfdd09cc6c2cd61140fa78f7a070b5eabd7ee259b0590403992",
                "25bf205ebb67e38337023dcf053f5fbff510e21bd9a64d6c9b6e6147427ce874",
            ],
            [
                "6d65ca9c6b82a619e92e4ecc49c093ce6371985455de7797d565b3adbe47fb14",
                "06ab1bde29031443dc420ec1fd7e54364b1b889dcb57f521811b3ab31008b17b",
                "4204cff3f16ee46f60255c99388156b0af55c2b993de7455e014017b9f9bb2b0",
            ],
            [
                "a486eed296b74d68f41b89e01096bf00a67b182786929dd797bf27ce1cdbf603",
                "0a85c062f9ae099f7ccc1a7f9c25aaf9e7f16a05a29df59135b5d0e42d134d30",
                "2c989afc991446f3cf71331eff1ee37bbbc49e9c12f2e49b443145a55622dd39",
            ],
            [
                "3b90019bbd326c6552db863aa21f13f32d406407f39b982fae1beb6767f23bbb",
                "c7ee0fde0e03cd8af75e87429c93322d568f4fa59869cbe29af1fe5f08b76d0a",
                "fd0ef1d480345f6f3f3e1bda84de96c910558bef25e16646d26fc92898570443",
            ],
        ];
        for (secret, row) in secrets.iter().zip(tags) {
            for (grant, want) in grants.iter().zip(row) {
                let cap = mint(secret, grant).unwrap();
                assert_eq!(hex(&cap.tag), want, "{}-byte secret, {grant}", secret.len());
                assert!(verify(secret, &cap));
            }
        }

        let cap = mint(b"broker-secret-key", "ro:/f/F/fleet/>").unwrap();
        let nonce: Vec<u8> = (0u8..32).collect();
        assert_eq!(
            hex(&attach_proof(&cap.tag, &nonce, "ro:/f/F/fleet/>")),
            "3f2e19fba0a70e487bce61a44ee2b173ec273bdd6f444a988d921e4c0e1a315b"
        );

        for (principal, want) in [
            (String::new(), 17_935_985_926_779_910_026),
            ("x".repeat(43), 18_257_435_040_005_927_146),
            ("y".repeat(44), 14_590_640_223_644_302_360),
            ("z".repeat(52), 10_940_676_290_768_544_027),
            ("w".repeat(53), 11_676_937_174_542_836_057),
            ("q".repeat(200), 1_749_860_932_688_955_062),
        ] {
            assert_eq!(
                producer_id_of(&principal),
                want,
                "{} bytes",
                principal.len()
            );
        }
    }

    #[test]
    fn valid_capability_verifies_and_grants_its_subtree() {
        let secret = b"broker-secret-key";
        let cap = mint(secret, "/a/stream/>").unwrap();
        assert!(verify(secret, &cap));
        assert!(grants(secret, &cap, "/a/stream/x", T0));
        assert!(grants(secret, &cap, "/a/stream/x/y", T0));
        // Outside the granted subtree: denied even though the cap is genuine.
        assert!(!grants(secret, &cap, "/a/inbox/x", T0));
    }

    #[test]
    fn forged_or_tampered_capabilities_are_rejected() {
        let secret = b"broker-secret-key";
        let cap = mint(secret, "/a/stream/>").unwrap();
        // Widen the filter but keep the old tag → tag mismatch → rejected.
        let tampered = Capability {
            filter: "/a/>".to_string(),
            tag: cap.tag,
        };
        assert!(!verify(secret, &tampered));
        assert!(!grants(secret, &tampered, "/a/inbox/x", T0));
        // A guessed tag is rejected.
        let forged = Capability {
            filter: "/a/>".to_string(),
            tag: [0u8; TAG],
        };
        assert!(!verify(secret, &forged));
        // The right filter under the WRONG secret is rejected.
        assert!(!verify(b"attacker-key", &cap));
    }

    #[test]
    fn a_bare_filter_is_the_read_write_unbound_grant() {
        let secret = b"broker-secret-key";
        let bare = "/a/stream/>";
        let g = Grant::parse(bare).unwrap();
        assert_eq!(g.mode, Mode::ReadWrite);
        assert_eq!(g.principal, None);
        assert_eq!(g.filter, bare);
        assert_eq!(mode_of(bare), Some(Mode::ReadWrite));

        // The tag is over the same message it always was, so a capability minted
        // before the prefix existed still verifies bit-for-bit.
        let cap = mint(secret, bare).unwrap();
        assert_eq!(cap.tag, hmac_sha256(secret, bare.as_bytes()));
        assert!(verify(secret, &cap));

        // Unbound: any producer id publishes, which is what makes it the god cap.
        assert!(grants_publish(secret, &cap, "/a/stream/x", 1, T0));
        assert!(grants_publish(secret, &cap, "/a/stream/x", u64::MAX, T0));
        assert!(!grants_publish(secret, &cap, "/a/inbox/x", 1, T0));
        assert!(grants_commit(secret, &cap, "/a/stream/g1", T0));
    }

    #[test]
    fn a_read_only_grant_reads_and_never_writes() {
        let secret = b"broker-secret-key";
        let grant = "ro:/f/F/fleet/>";
        // The prefix is safe precisely because it cannot parse as a filter.
        assert!(Filter::new(grant).is_err());

        let cap = mint(secret, grant).unwrap();
        assert!(verify(secret, &cap));
        assert_eq!(mode_of(grant), Some(Mode::ReadOnly));
        assert_eq!(Grant::parse(grant).unwrap().filter, "/f/F/fleet/>");

        // Reads: the whole granted subtree.
        assert!(grants_filter(secret, &cap, "/f/F/fleet/h-andrew/halt", T0));
        assert!(grants_filter(secret, &cap, "/f/F/fleet/>", T0));
        assert!(!grants_filter(secret, &cap, "/f/F/pub/>", T0));

        // Writes: none, anywhere, including through the legacy entry point.
        assert!(!grants_publish(
            secret,
            &cap,
            "/f/F/fleet/h-andrew/halt",
            7,
            T0
        ));
        assert!(!grants_commit(secret, &cap, "/f/F/fleet/g1", T0));
        assert!(!grants(secret, &cap, "/f/F/fleet/h-andrew/halt", T0));
    }

    #[test]
    fn a_bound_grant_publishes_only_as_the_derived_producer_id() {
        let secret = b"broker-secret-key";
        let node = "n-a1b2c3d4e5f60718";
        let grant = "rw,p=n-a1b2c3d4e5f60718:/f/F/in/*/*/n-a1b2c3d4e5f60718/*";
        let parsed = Grant::parse(grant).unwrap();
        assert_eq!(parsed.mode, Mode::ReadWrite);
        assert_eq!(parsed.principal.as_deref(), Some(node));

        let cap = mint(secret, grant).unwrap();
        let pid = producer_id_of(node);
        let subject = "/f/F/in/n-b/s-c/n-a1b2c3d4e5f60718/ask";
        assert!(grants_publish(secret, &cap, subject, pid, T0));
        // A bearer that names any other producer id is refused: this is the
        // dedup-key poisoning hole, closed.
        assert!(!grants_publish(
            secret,
            &cap,
            subject,
            pid.wrapping_add(1),
            T0
        ));
        assert!(!grants_publish(
            secret,
            &cap,
            subject,
            producer_id_of("h-andrew"),
            T0
        ));
        assert!(!grants_publish(secret, &cap, subject, 0, T0));
        // Still scoped by the filter, under the right id.
        assert!(!grants_publish(
            secret,
            &cap,
            "/f/F/in/n-b/s-c/h-andrew/ask",
            pid,
            T0
        ));
        // The `*` kind segment: an 8-segment subject is outside the grant.
        assert!(!grants_publish(
            secret,
            &cap,
            "/f/F/in/n-b/s-c/n-a1b2c3d4e5f60718/h-andrew/answer",
            pid,
            T0
        ));
    }

    #[test]
    fn producer_ids_are_domain_separated_sha256_and_distinct_per_principal() {
        // Fixed vectors: the derivation is part of the wire contract (a broker and
        // a bridge must agree on it), so it is pinned, not merely round-tripped.
        assert_eq!(
            producer_id_of("n-a1b2c3d4e5f60718"),
            2_992_018_643_546_584_750
        );
        assert_eq!(producer_id_of("h-andrew"), 9_245_449_477_876_580_480);
        assert_ne!(producer_id_of("h-andrew"), producer_id_of("h-andrea"));
        assert_ne!(producer_id_of("h-andrew"), producer_id_of("a-andrew"));

        // Independently recomputed from the stated construction, domain first.
        let mut h = Sha256::new();
        h.update(b"astream-pid\0");
        h.update(b"s-0123456789abcdef0123");
        let d = h.finalize();
        let mut head = [0u8; 8];
        head.copy_from_slice(&d[..8]);
        assert_eq!(
            producer_id_of("s-0123456789abcdef0123"),
            u64::from_le_bytes(head)
        );

        // The domain separator is load-bearing: an undomained hash differs.
        let plain = Sha256::digest(b"h-andrew");
        let mut plain_head = [0u8; 8];
        plain_head.copy_from_slice(&plain[..8]);
        assert_ne!(producer_id_of("h-andrew"), u64::from_le_bytes(plain_head));
    }

    #[test]
    fn a_widened_mode_or_a_swapped_principal_with_the_old_tag_is_rejected() {
        let secret = b"broker-secret-key";
        let ro = mint(secret, "ro:/f/F/fleet/>").unwrap();
        // Flip the mode to read-write, keep the tag: the tag covers the WHOLE
        // grant string, so the mode is as unforgeable as the filter.
        let widened = Capability {
            filter: "rw:/f/F/fleet/>".to_string(),
            tag: ro.tag,
        };
        assert!(!verify(secret, &widened));
        assert!(!grants_publish(
            secret,
            &widened,
            "/f/F/fleet/h-a/halt",
            1,
            T0
        ));
        assert!(!grants_filter(secret, &widened, "/f/F/fleet/>", T0));

        let bound = mint(secret, "rw,p=h-andrew:/f/F/fleet/h-andrew/>").unwrap();
        // Swap the principal for one whose id the attacker controls.
        let swapped = Capability {
            filter: "rw,p=h-mallory:/f/F/fleet/h-andrew/>".to_string(),
            tag: bound.tag,
        };
        assert!(!verify(secret, &swapped));
        assert!(!grants_publish(
            secret,
            &swapped,
            "/f/F/fleet/h-andrew/halt",
            producer_id_of("h-mallory"),
            T0
        ));
        // Drop the binding entirely to reach the unbound god-cap branch.
        let unbound = Capability {
            filter: "rw:/f/F/fleet/h-andrew/>".to_string(),
            tag: bound.tag,
        };
        assert!(!verify(secret, &unbound));
        assert!(!grants_publish(
            secret,
            &unbound,
            "/f/F/fleet/h-andrew/halt",
            9,
            T0
        ));
        // Widen the filter half under a genuine prefix.
        let wide = Capability {
            filter: "rw,p=h-andrew:/f/F/>".to_string(),
            tag: bound.tag,
        };
        assert!(!verify(secret, &wide));
        // And the genuine grant under the wrong secret authorizes nothing.
        assert!(!verify(b"attacker-key", &bound));
        assert!(!grants_publish(
            b"attacker-key",
            &bound,
            "/f/F/fleet/h-andrew/halt",
            producer_id_of("h-andrew"),
            T0
        ));
    }

    #[test]
    fn grant_parse_refuses_malformed_grants() {
        for bad in [
            "",                               // empty
            "not-a-grant",                    // no prefix, no leading slash
            "f/F/pub",                        // a filter without its leading slash
            "ro:",                            // empty filter half
            "ro:f/F/pub",                     // filter half without leading slash
            "ro:/f//pub",                     // empty segment
            "ro:/f/F/pub/>/x",                // `>` not last
            "ro:/f/F/pu*b",                   // partial wildcard
            "rwx:/f/F/pub/>",                 // unknown mode
            "RW:/f/F/pub/>",                  // modes are lowercase literals
            "rw,h-andrew:/f/F/pub/>",         // principal without `p=`
            "rw,p=andrew:/f/F/pub/>",         // no class prefix
            "rw,p=x-andrew:/f/F/pub/>",       // unknown class
            "rw,p=h-:/f/F/pub/>",             // empty name
            "rw,p=h-Andrew:/f/F/pub/>",       // uppercase outside [a-z0-9-]
            "rw,p=h-and_rew:/f/F/pub/>",      // underscore outside [a-z0-9-]
            "rw,p=h-and/rew:/f/F/pub/>",      // a `/` would break the subject grammar
            "rw,p=h-and:rew:/f/F/pub/>",      // a `:` in the principal
            "rw,p=h-andrew,p=h-m:/f/F/pub/>", // a second binding
        ] {
            assert!(
                Grant::parse(bad).is_err(),
                "{bad:?} must not parse as a grant"
            );
            assert!(mint(b"secret", bad).is_err(), "{bad:?} must not mint");
            assert_eq!(mode_of(bad), None, "{bad:?} has no mode");
        }
        // An aterm tab ID is a session's principal; every near miss is refused.
        let tab = "rw,p=tqn5r6e0148:/f/F/pub/>";
        assert_eq!(
            Grant::parse(tab).map(|g| g.principal),
            Ok(Some("tqn5r6e0148".to_string()))
        );
        for near in [
            "tqn5r6e014",   // 10 bytes
            "tqn5r6e01488", // 12 bytes
            "tqn5r6e014i",  // Crockford excludes i, l, o and u
            "tqn5r6e014u",
            "tQN5R6E0148", // upper case
            "xqn5r6e0148", // not `t`
        ] {
            assert!(
                Grant::parse(&format!("rw,p={near}:/f/F/pub/>")).is_err(),
                "{near:?} is not a principal"
            );
        }
        // A 32-character name is the boundary; 33 is over it.
        let name32 = "h-".to_string() + &"a".repeat(32);
        assert!(Grant::parse(&format!("rw,p={name32}:/f/F/pub/>")).is_ok());
        let name33 = "h-".to_string() + &"a".repeat(33);
        assert!(Grant::parse(&format!("rw,p={name33}:/f/F/pub/>")).is_err());

        // A genuinely-tagged string that is not a grant authorizes nothing: the
        // parse is fail-closed, never a fall-through to "unrestricted".
        let secret = b"broker-secret-key";
        let junk = "rwx:/f/F/pub/>";
        let genuine_tag = Capability {
            filter: junk.to_string(),
            tag: hmac_sha256(secret, junk.as_bytes()),
        };
        assert!(verify(secret, &genuine_tag), "the tag itself is genuine");
        assert!(!grants(secret, &genuine_tag, "/f/F/pub/x", T0));
        assert!(!grants_publish(secret, &genuine_tag, "/f/F/pub/x", 1, T0));
        assert!(!grants_commit(secret, &genuine_tag, "/f/F/pub/x", T0));
        assert!(!grants_filter(secret, &genuine_tag, "/f/F/pub/x", T0));
    }

    #[test]
    fn attach_proof_is_bound_to_the_nonce_the_tag_and_the_grant() {
        let secret = b"broker-secret-key";
        let grant = "rw,p=n-a1b2c3d4e5f60718:/f/F/pub/n-a1b2c3d4e5f60718/>";
        let cap = mint(secret, grant).unwrap();
        let nonce = [7u8; 32];
        let proof = attach_proof(&cap.tag, &nonce, grant);

        assert!(verify_attach(secret, grant, &nonce, &proof));
        // The proof is not the tag: what crosses the wire never reveals it.
        assert_ne!(proof, cap.tag);

        // A captured Attach replayed on a second connection (a fresh nonce) fails.
        let other_nonce = [8u8; 32];
        assert!(!verify_attach(secret, grant, &other_nonce, &proof));
        // ... and one flipped nonce byte is enough.
        let mut near = nonce;
        near[31] ^= 0x01;
        assert!(!verify_attach(secret, grant, &near, &proof));

        // A proof for one grant cannot be presented for another, even one the same
        // secret would happily mint.
        let sibling = "rw,p=n-a1b2c3d4e5f60718:/f/F/cur/n-a1b2c3d4e5f60718/>";
        assert!(!verify_attach(secret, sibling, &nonce, &proof));
        // Widening the grant at attach time fails too.
        assert!(!verify_attach(secret, "/f/F/>", &nonce, &proof));

        // A proof computed from a guessed tag, from another cap's tag, or under
        // the wrong secret is refused.
        let guessed = attach_proof(&[0u8; TAG], &nonce, grant);
        assert!(!verify_attach(secret, grant, &nonce, &guessed));
        let elsewhere = mint(secret, sibling).unwrap();
        assert!(!verify_attach(
            secret,
            grant,
            &nonce,
            &attach_proof(&elsewhere.tag, &nonce, grant)
        ));
        assert!(!verify_attach(b"attacker-key", grant, &nonce, &proof));

        // A truncated or over-long proof is a mismatch, never a panic.
        assert!(!verify_attach(secret, grant, &nonce, &proof[..31]));
        assert!(!verify_attach(secret, grant, &nonce, &[]));
        let mut long = proof.to_vec();
        long.push(0);
        assert!(!verify_attach(secret, grant, &nonce, &long));

        // A grant string that is not a grant is refused before the MAC is trusted.
        let junk = "rwx:/f/F/pub/>";
        let junk_tag = hmac_sha256(secret, junk.as_bytes());
        assert!(!verify_attach(
            secret,
            junk,
            &nonce,
            &attach_proof(&junk_tag, &nonce, junk)
        ));
    }

    /// The structural guard behind "no early exit on the first differing byte",
    /// on the primitive itself. For every ordered pair of mismatch positions, the
    /// fold must carry the LATER byte's difference as well as the earlier one: an
    /// implementation that returned as soon as it found a difference (or delegated
    /// to `a == b`, which is free to) would report only the difference at `i` and
    /// fail here. `verify_folds_every_byte_of_the_tag` and
    /// `verify_attach_folds_every_byte_of_the_proof` pin the same shape on the
    /// functions the security path calls. The shape of the compare, not its timing.
    #[test]
    fn ct_diff_folds_every_byte_whatever_the_mismatch() {
        let a = [0u8; TAG];
        for i in 0..TAG {
            for j in (i + 1)..TAG {
                let mut b = a;
                b[i] = 0x01; // an early difference ...
                b[j] = 0x02; // ... and a later one, in a bit the first does not set
                assert_eq!(
                    ct_diff(&a, &b),
                    0x03,
                    "byte {j} was not folded in: the compare exits at the mismatch at {i}"
                );
            }
        }
        // A difference in the last byte alone is still seen, and equal tags fold to
        // zero — the two ends the loop is easiest to get wrong at.
        let mut last = a;
        last[TAG - 1] = 0x80;
        assert_eq!(ct_diff(&a, &last), 0x80);
        assert_eq!(ct_diff(&a, &a), 0);
    }

    /// The behaviour at the public entry point: a proof that differs from the
    /// genuine one in any single byte — first, last, or anywhere between — is
    /// refused. (An early-exit compare would pass this too; the fold tests are
    /// what tell the two apart.)
    #[test]
    fn verify_attach_refuses_a_proof_differing_in_any_single_byte() {
        let secret = b"broker-secret-key";
        let grant = "rw,p=n-a1b2c3d4e5f60718:/f/F/pub/n-a1b2c3d4e5f60718/>";
        let cap = mint(secret, grant).unwrap();
        let nonce = [7u8; 32];
        let proof = attach_proof(&cap.tag, &nonce, grant);
        assert!(verify_attach(secret, grant, &nonce, &proof));
        for i in 0..TAG {
            let mut near = proof;
            near[i] ^= 0x01;
            assert!(
                !verify_attach(secret, grant, &nonce, &near),
                "a proof differing only in byte {i} was accepted"
            );
        }
    }

    /// The same fold, pinned on the function the MINT check decides on. `verify` is
    /// `verify_diff(..) == 0` and nothing else, so what this asserts about
    /// `verify_diff` is what the compare behind `verify` does: for every ordered
    /// pair of tampered byte positions the returned fold carries the LATER byte's
    /// difference as well as the earlier one, which a compare that stopped at the
    /// first difference — `a == b` included — could not report. (A rewrite that
    /// bypasses `verify_diff` is caught by `deny(dead_code)` instead.)
    #[test]
    fn verify_folds_every_byte_of_the_tag() {
        let secret = b"broker-secret-key";
        let cap = mint(secret, "rw:/f/F/pub/>").unwrap();
        assert_eq!(verify_diff(secret, &cap), 0);
        assert!(verify(secret, &cap));
        for i in 0..TAG {
            for j in (i + 1)..TAG {
                let mut forged = cap.clone();
                forged.tag[i] ^= 0x01; // an early difference ...
                forged.tag[j] ^= 0x02; // ... and a later one, in a bit the first misses
                assert_eq!(
                    verify_diff(secret, &forged),
                    0x03,
                    "verify's compare dropped tag byte {j}: it exits at the mismatch at {i}"
                );
                assert!(!verify(secret, &forged));
            }
        }
    }

    /// The same fold, pinned on the function the ATTACH check decides on.
    /// `verify_attach` is `verify_attach_diff(..) == Some(0)` and nothing else. The
    /// `None` arms are the two cases with nothing to fold: a grant that does not
    /// parse (no MAC is trusted) and a proof of the wrong length (refused on the
    /// length alone, never a panic).
    #[test]
    fn verify_attach_folds_every_byte_of_the_proof() {
        let secret = b"broker-secret-key";
        let grant = "rw,p=n-a1b2c3d4e5f60718:/f/F/pub/n-a1b2c3d4e5f60718/>";
        let cap = mint(secret, grant).unwrap();
        let nonce = [7u8; 32];
        let proof = attach_proof(&cap.tag, &nonce, grant);
        assert_eq!(verify_attach_diff(secret, grant, &nonce, &proof), Some(0));
        assert!(verify_attach(secret, grant, &nonce, &proof));
        for i in 0..TAG {
            for j in (i + 1)..TAG {
                let mut near = proof;
                near[i] ^= 0x01;
                near[j] ^= 0x02;
                assert_eq!(
                    verify_attach_diff(secret, grant, &nonce, &near),
                    Some(0x03),
                    "the attach compare dropped proof byte {j}: it exits at the mismatch at {i}"
                );
                assert!(!verify_attach(secret, grant, &nonce, &near));
            }
        }
        // Nothing to fold: a wrong length.
        assert_eq!(
            verify_attach_diff(secret, grant, &nonce, &proof[..TAG - 1]),
            None
        );
        let mut long = proof.to_vec();
        long.push(0);
        assert_eq!(verify_attach_diff(secret, grant, &nonce, &long), None);
        // A string that is not a grant: refused as None under a GENUINE proof
        // (no MAC is trusted for it), and as an ordinary mismatch under any
        // other, because it is only parsed once its proof has matched.
        let junk = "rwx:/f/F/pub/>";
        let junk_proof = attach_proof(&hmac_sha256(secret, junk.as_bytes()), &nonce, junk);
        assert_eq!(verify_attach_diff(secret, junk, &nonce, &junk_proof), None);
        assert_ne!(verify_attach_diff(secret, junk, &nonce, &proof), Some(0));
        assert!(verify_attach_diff(secret, junk, &nonce, &proof).is_some());
    }

    /// The grammar: `exp=` is a prefix field beside `p=`, in either order, and
    /// every string that was a grant before this field existed still is one with
    /// no expiry. That last half is what keeps already-minted capabilities valid.
    #[test]
    fn an_expiry_is_a_prefix_field_and_every_older_grant_still_parses() {
        let g = Grant::parse("rw,exp=1700000000000:/f/lab/>").expect("exp alone");
        assert_eq!(g.expires_at, Some(1_700_000_000_000));
        assert_eq!(g.mode, Mode::ReadWrite);
        assert_eq!(g.principal, None);

        // Either order, and both fields together.
        for text in [
            "rw,p=n-lab,exp=1700000000000:/f/lab/>",
            "rw,exp=1700000000000,p=n-lab:/f/lab/>",
        ] {
            let g = Grant::parse(text).unwrap_or_else(|e| panic!("{text}: {e}"));
            assert_eq!(g.expires_at, Some(1_700_000_000_000), "{text}");
            assert_eq!(g.principal.as_deref(), Some("n-lab"), "{text}");
        }

        // EVERY shape that predates the field: no expiry, and never expiring.
        for older in [
            "/f/lab/>",
            "rw:/f/lab/>",
            "ro:/f/lab/>",
            "rw,p=n-lab:/f/lab/>",
        ] {
            let g = Grant::parse(older).unwrap_or_else(|e| panic!("{older}: {e}"));
            assert_eq!(g.expires_at, None, "{older}");
            assert!(!is_expired(older, u64::MAX), "{older} must never expire");
        }
        assert_eq!(expires_at("rw,exp=7:/f/lab/>"), Some(7));
        assert_eq!(expires_at("rw:/f/lab/>"), None);
    }

    /// A malformed expiry is a REFUSAL, never a default. A grant that quietly
    /// dropped an unreadable `exp=` would be a capability that outlives the
    /// authority its author wrote down.
    #[test]
    fn a_malformed_expiry_is_refused_rather_than_defaulted() {
        for bad in [
            "rw,exp=:/f/lab/>",                        // empty
            "rw,exp=abc:/f/lab/>",                     // not digits
            "rw,exp=+7:/f/lab/>",                      // u64::from_str would accept this
            "rw,exp=-7:/f/lab/>",                      // ditto for the sign
            "rw,exp=7 :/f/lab/>",                      // trailing space
            "rw,exp=99999999999999999999999:/f/lab/>", // overflows u64
            "rw,exp=1,exp=2:/f/lab/>",                 // repeated: not a last-wins grammar
            "rw,p=n-a,p=n-b:/f/lab/>",                 // the same rule for the older field
            "rw,ttl=60:/f/lab/>",                      // an unknown field is never ignored
        ] {
            assert!(Grant::parse(bad).is_err(), "{bad} must not parse");
            // And the gate agrees: an unparseable grant is EXPIRED, not eternal.
            assert!(is_expired(bad, 0), "{bad} must fail closed");
        }
    }

    /// Half-open, like every other range here: valid at `exp - 1`, expired AT
    /// `exp`. Spelling "valid until midnight" has exactly one right answer.
    #[test]
    fn expiry_is_half_open_at_the_instant_itself() {
        let grant = "rw,exp=1000:/f/lab/>";
        assert!(!is_expired(grant, 0));
        assert!(!is_expired(grant, 999));
        assert!(is_expired(grant, 1000), "exp is the first INVALID instant");
        assert!(is_expired(grant, 1001));
    }

    /// An expired capability authorizes NOTHING — not a write, not a publish,
    /// not a commit, not a subscribe. All four predicates reach authority through
    /// one place, and this pins that none of them has its own way in.
    #[test]
    fn an_expired_capability_authorizes_nothing_on_any_path() {
        let secret = b"broker-secret";
        let cap = mint(secret, "rw,p=n-lab,exp=1000:/f/lab/>").expect("mint");
        let pid = producer_id_of("n-lab");

        // One millisecond before: every path authorizes.
        assert!(grants(secret, &cap, "/f/lab/pub", 999));
        assert!(grants_publish(secret, &cap, "/f/lab/pub", pid, 999));
        assert!(grants_commit(secret, &cap, "/f/lab/g1", 999));
        assert!(grants_filter(secret, &cap, "/f/lab/>", 999));

        // At the instant itself, and after: none of them does.
        for now in [1000u64, 1001, u64::MAX] {
            assert!(!grants(secret, &cap, "/f/lab/pub", now), "grants @{now}");
            assert!(
                !grants_publish(secret, &cap, "/f/lab/pub", pid, now),
                "grants_publish @{now}"
            );
            assert!(
                !grants_commit(secret, &cap, "/f/lab/g1", now),
                "grants_commit @{now}"
            );
            assert!(
                !grants_filter(secret, &cap, "/f/lab/>", now),
                "grants_filter @{now}"
            );
        }
        // The capability is still GENUINE — expiry is not forgery, and `verify`
        // is not the gate. A caller that only checked `verify` would be wrong,
        // which is why nothing in this crate authorizes through it alone.
        assert!(verify(secret, &cap));
    }

    /// THE SECURITY PROPERTY, and the reason this needed no new crypto: the tag
    /// is HMAC over the WHOLE grant string, so the expiry is inside the signed
    /// material. A bearer who edits the number to buy themselves more time holds
    /// a capability that no longer verifies — and cannot mint the right tag
    /// without the secret.
    #[test]
    fn the_expiry_cannot_be_extended_stripped_or_shortened_without_the_secret() {
        let secret = b"broker-secret";
        let honest = mint(secret, "rw,exp=1000:/f/lab/>").expect("mint");

        // Extend it: same tag, later deadline.
        let extended = Capability {
            filter: "rw,exp=99999999:/f/lab/>".to_string(),
            tag: honest.tag,
        };
        assert!(
            !verify(secret, &extended),
            "an extended expiry must not verify"
        );
        assert!(!grants(secret, &extended, "/f/lab/pub", 2000));

        // Strip it entirely: the eternal capability nobody granted.
        let stripped = Capability {
            filter: "rw:/f/lab/>".to_string(),
            tag: honest.tag,
        };
        assert!(
            !verify(secret, &stripped),
            "a stripped expiry must not verify"
        );
        assert!(!grants(secret, &stripped, "/f/lab/pub", 2000));

        // And the other direction, because a capability is not only the bearer's
        // to weaken: a third party must not be able to shorten someone's grant.
        let shortened = Capability {
            filter: "rw,exp=1:/f/lab/>".to_string(),
            tag: honest.tag,
        };
        assert!(!verify(secret, &shortened));

        // Only the secret-holder can reissue, and the reissue is a DIFFERENT tag.
        let reissued = mint(secret, "rw,exp=99999999:/f/lab/>").expect("reissue");
        assert!(verify(secret, &reissued));
        assert_ne!(reissued.tag, honest.tag);
        assert!(grants(secret, &reissued, "/f/lab/pub", 2000));
    }

    /// The attach proof covers the expiry too, because it is computed over the
    /// grant string: a bearer cannot present a genuine tag under an edited
    /// deadline, which is the shape `verify_attach` already refused for filters.
    #[test]
    fn an_attach_proof_does_not_carry_across_an_edited_expiry() {
        let secret = b"broker-secret";
        let grant = "rw,exp=1000:/f/lab/>";
        let cap = mint(secret, grant).expect("mint");
        let nonce = [7u8; 32];
        let proof = attach_proof(&cap.tag, &nonce, grant);
        assert!(verify_attach(secret, grant, &nonce, &proof));
        assert!(!verify_attach(
            secret,
            "rw,exp=99999999:/f/lab/>",
            &nonce,
            &proof
        ));
    }

    /// An attach proof over a chosen 32-byte challenge must never become a bearer
    /// tag in the offline-attenuation context, even for an equal-authority child.
    #[test]
    fn a_chosen_attach_challenge_is_not_an_offline_bearer_tag() {
        let secret = b"synthetic context separation secret";
        let parent = mint(secret, "/a").expect("root");
        assert!(verify(secret, &parent));
        let child = attenuate_offline(&parent, "rw:/a", 0).expect("equal-authority child");
        assert_eq!(child.filter, "rw,via=2f61:/a");
        assert!(verify(secret, &child), "ordinary offline child is accepted");
        let ordinary_nonce = [7u8; 32];
        let ordinary_proof = attach_proof(&child.tag, &ordinary_nonce, &child.filter);
        assert!(verify_attach(
            secret,
            &child.filter,
            &ordinary_nonce,
            &ordinary_proof
        ));

        // This is the old v1 message collision: 20 domain bytes + 12 prefix bytes
        // make a legal 32-byte nonce. The subsequent grant is the parent's /a.
        let mut chosen_nonce = [0u8; 32];
        chosen_nonce[..20].copy_from_slice(b"astream-macaroon-v1\0");
        chosen_nonce[20..].copy_from_slice(b"rw,via=2f61:");
        let proof = attach_proof(&parent.tag, &chosen_nonce, &parent.filter);
        let substituted = Capability {
            filter: child.filter.clone(),
            tag: proof,
        };
        let substituted_proof = attach_proof(&proof, &ordinary_nonce, &child.filter);
        let same_tag = child.tag == proof;
        let accepted_bearer = verify(secret, &substituted);
        let accepted_attach =
            verify_attach(secret, &child.filter, &ordinary_nonce, &substituted_proof);
        assert_eq!(
            (same_tag, accepted_bearer, accepted_attach),
            (false, false, false)
        );
    }

    /// Issuance and verification share the same chained-grant byte bound. A child
    /// past that bound is an explicit refusal, never an unusable accepted cap.
    #[test]
    fn offline_issuance_refuses_a_child_beyond_the_verifiers_bound() {
        let secret = b"synthetic issuance bound secret";
        let parent = mint(secret, "/f/>").expect("root");
        let small = attenuate_offline(&parent, "rw:/f/a", 0).expect("small child");
        assert!(verify(secret, &small));

        // Existing verification threshold; the new shared constant must preserve it.
        let bound = MAX_VIA_HEX_LEN + 512;
        let overhead = "rw,via=".len() + 2 * parent.filter.len() + 1;
        let at_filter = format!("/f/{}", "a".repeat(bound - overhead - "/f/".len()));
        let at = attenuate_offline(&parent, &format!("rw:{at_filter}"), 0).expect("at bound");
        assert_eq!(at.filter.len(), bound);
        assert!(verify(secret, &at), "accepted boundary child verifies");

        let over_grant = format!("rw:{at_filter}a");
        assert!(Grant::parse(&over_grant).is_ok(), "valid filter grammar");
        assert!(
            can_attenuate(&parent.filter, &over_grant).is_ok(),
            "valid narrowing"
        );
        let direct = mint(secret, &over_grant).expect("root issuer retains long ordinary grants");
        assert!(
            verify(secret, &direct),
            "ordinary non-via root tags are unchanged"
        );
        let over = attenuate_offline(&parent, &over_grant, 0);
        let returned_error = over.is_err();
        let returned_unverifiable = over.as_ref().is_ok_and(|cap| !verify(secret, cap));
        assert_eq!((returned_error, returned_unverifiable), (true, false));
    }

    #[test]
    fn offline_attenuation_keeps_utf8_parent_filters_and_rejects_invalid_utf8() {
        let secret = b"synthetic Unicode attenuation secret";
        let now_ms = 1000;

        let ascii = mint(secret, "rw:/cafe/>").expect("ASCII parent");
        let ascii_child = attenuate_offline(&ascii, "rw:/cafe/topic", now_ms).expect("ASCII child");
        assert!(verify(secret, &ascii_child));
        assert_eq!(
            parent_grant(&ascii_child.filter).as_deref(),
            Some("rw:/cafe/>")
        );
        assert!(grants_publish(
            secret,
            &ascii_child,
            "/cafe/topic",
            7,
            now_ms
        ));
        assert!(!grants_publish(
            secret,
            &ascii_child,
            "/cafe/other",
            7,
            now_ms
        ));
        assert!(attenuate_offline(&ascii, "rw:/elsewhere/topic", now_ms).is_err());

        // Hex is lowercase and byte-paired, but these parent byte strings are not UTF-8.
        for via in ["ff", "c3", "c328"] {
            assert!(mint(secret, &format!("rw,via={via}:/cafe/topic")).is_err());
        }
        for via in ["0", "GG"] {
            assert!(mint(secret, &format!("rw,via={via}:/cafe/topic")).is_err());
        }

        let parent_grant_text = "rw:/café/>";
        let parent = mint(secret, parent_grant_text).expect("valid UTF-8 parent filter");
        assert!(verify(secret, &parent));
        assert!(grants_publish(secret, &parent, "/café/topic", 7, now_ms));
        let child = attenuate_offline(&parent, "rw:/café/topic", now_ms);
        let roundtrip = child.as_ref().is_ok_and(|child| {
            parent_grant(&child.filter).as_deref() == Some(parent_grant_text)
                && verify(secret, child)
                && grants_publish(secret, child, "/café/topic", 7, now_ms)
                && !grants_publish(secret, child, "/café/other", 7, now_ms)
                && !grants_publish(secret, child, "/cafe/topic", 7, now_ms)
        });
        assert!(
            roundtrip,
            "ASTREAM_CAP_UTF8_OFFLINE_PARENT_CHAIN_FAILED: {child:?}"
        );
    }

    #[test]
    fn a_relay_field_parses_once_and_only_on_a_write_grant() {
        let g = Grant::parse("rw,relay,p=n-a1:/m/>").unwrap();
        assert!(g.relay);
        assert!(!Grant::parse("rw,p=n-a1:/m/>").unwrap().relay);
        assert!(Grant::parse("rw,relay,relay:/m/>").is_err());
        assert!(Grant::parse("ro,relay:/m/>").is_err());
    }

    #[test]
    fn a_subject_owner_is_the_segment_that_says_whose_it_is() {
        for (subject, owner) in [
            ("/t/rows/n-a1", Some("n-a1")),
            ("/t/rows/n-a1/k", Some("n-a1")),
            ("/m/n-a1", Some("n-a1")),
            ("/m/n-a1/cpu/5m", Some("n-a1")),
            ("/f/lab/pub/n-a1/s-1/ev", Some("n-a1")),
            ("/f/lab/cur/n-a1/c", Some("n-a1")),
            ("/f/lab/halt/n-a1/now", Some("n-a1")),
            // A shape with no owner, or an owner of the wrong class.
            ("/t/rows", None),
            ("/t/rows/h-amy", None),
            ("/m/h-amy/x", None),
            ("/m", None),
            ("/f/lab/pub/s-1", None),
            ("/f/lab/pub/p/n-a1", None),
            ("/f/lab/fleet/n-a1", None),
            ("/f/lab/in/human/h-amy/n-a1", None),
            ("/f/lab/in/human/h-amy/n-a1/note/more", None),
            ("/f/lab/other/n-a1", None),
            ("/x/n-a1", None),
            ("/g/relay/1", None),
        ] {
            assert_eq!(relay_owner(subject), owner, "{subject}");
        }
    }

    #[test]
    fn a_relay_writes_under_the_owners_id_and_only_through_grants_relay() {
        let secret = b"s";
        let a = producer_id_of("n-a1");
        let relay = mint(secret, "rw,relay,p=n-c1:/m/>").unwrap();
        assert!(grants_relay(secret, &relay, "/m/n-a1/x", a, 0));
        assert!(!grants_relay(
            secret,
            &relay,
            "/m/n-a1/x",
            producer_id_of("n-c1"),
            0
        ));
        assert!(!grants_relay(secret, &relay, "/m/n-b1/x", a, 0));
        assert!(
            !grants_relay(secret, &relay, "/t/rows/n-a1", a, 0),
            "filter"
        );
        assert!(
            !grants_relay(secret, &relay, "/m/plain/x", a, 0),
            "no owner"
        );
        // No other write.
        assert!(!grants(secret, &relay, "/m/n-a1/x", 0));
        assert!(!grants_commit(secret, &relay, "/m/n-a1/g", 0));
        assert!(!grants_publish(
            secret,
            &relay,
            "/m/n-c1/x",
            producer_id_of("n-c1"),
            0
        ));
        // Reading is a read.
        assert!(grants_filter(secret, &relay, "/m/>", 0));

        let bound = mint(secret, "rw,p=n-a1:/m/n-a1/>").unwrap();
        assert!(!grants_relay(secret, &bound, "/m/n-a1/x", a, 0));
        let read = mint(secret, "ro:/m/>").unwrap();
        assert!(!grants_relay(secret, &read, "/m/n-a1/x", a, 0));
        let root = mint(secret, "rw:/>").unwrap();
        assert!(grants_relay(secret, &root, "/m/n-a1/x", a, 0));
        assert!(!grants_relay(secret, &root, "/m/n-a1/x", 1, 0));
        let lapsed = mint(secret, "rw,relay,exp=10:/m/>").unwrap();
        assert!(grants_relay(secret, &lapsed, "/m/n-a1/x", a, 9));
        assert!(!grants_relay(secret, &lapsed, "/m/n-a1/x", a, 10));
    }

    #[test]
    fn a_relay_attenuates_to_a_narrower_relay_or_a_read() {
        let secret = b"s";
        let root = mint(secret, "rw:/>").unwrap();
        let relay = attenuate(secret, &root, "rw,relay:/m/>", 0).unwrap();
        let narrower = attenuate(secret, &relay, "rw,relay:/m/n-a1/>", 0).unwrap();
        assert!(grants_relay(
            secret,
            &narrower,
            "/m/n-a1/x",
            producer_id_of("n-a1"),
            0
        ));
        assert!(!grants_relay(
            secret,
            &narrower,
            "/m/n-b1/x",
            producer_id_of("n-b1"),
            0
        ));
        attenuate(secret, &relay, "ro:/m/>", 0).unwrap();

        // Not into a publish, nor out of a principal's own writes.
        assert!(attenuate(secret, &relay, "rw:/m/>", 0).is_err());
        assert!(attenuate(secret, &relay, "rw,p=n-a1:/m/n-a1/>", 0).is_err());
        let bound = mint(secret, "rw,p=n-a1:/m/n-a1/>").unwrap();
        assert!(attenuate(secret, &bound, "rw,relay,p=n-a1:/m/n-a1/>", 0).is_err());

        let offline = attenuate_offline(&relay, "rw,relay:/m/n-a1/>", 0).unwrap();
        assert!(grants_relay(
            secret,
            &offline,
            "/m/n-a1/x",
            producer_id_of("n-a1"),
            0
        ));
        assert!(!grants_relay(
            secret,
            &offline,
            "/m/n-b1/x",
            producer_id_of("n-b1"),
            0
        ));
    }
}
