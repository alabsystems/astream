//! Fabric receipts (`REQUIREMENTS` R8, `DESIGN-aterm-fabric` §4.1, §4.2 `ack`, §6.4 `dl=` /
//! `expired`): [`V1Receipt`], the view of the `ack` and `expired` records the bridges write
//! on an `in` lane, and [`FabricReceipt`], a header-first grammar no writer emits, kept for
//! the Clean-origin kernels it is built on.
//!
//! ## What is on the bus: [`V1Receipt`]
//!
//! A receipt on a real fabric is an `in`-lane record, `/f/<F>/in/<node>/<sid>/<src>/<kind>`,
//! whose body is a §4.1 `v=1 key=value` line. Its KIND is that subject's last segment, never
//! a word in the body. [`V1Receipt::decode`] reads one under the kind its subject names:
//!
//! ```text
//! ack      v=1 t=<ms> re=<off> [verdict=handled|refused|deferred]
//! expired  v=1 t=<ms> re=<off> dl=<ms>
//! ```
//!
//! - `re=` is the log offset of the `ask` or `task` the record settles.
//! - `verdict=`, on an `ack`, is what the recipient did with it, one of
//!   [`ReceiptVerdict::ALL`]. It is OPTIONAL. The receipt a recipient's bridge writes on
//!   `inbox seen` carries one, and so does `asb ack`'s line. A session's own
//!   `post kind=ack re=<off>` carries none: its words are in `text=`. The asker's bridge
//!   counts both as settling the ask, as it counts an `answer` or a `report`, so the view
//!   reads both. A verdict-less `ack` is [`V1Receipt::Ack`] with `verdict: None`.
//! - `dl=`, on an `expired`, is the deadline the ask carried. It is RELATIVE: a span in ms
//!   that the asker's bridge counts from when it recorded the ask, on its own clock. It is
//!   not an instant, so nothing here can hold it against a time.
//! - `t=` is the SENDER's wall clock, informational ([`V1Receipt::sender_t_ms`]). A broker's
//!   own time, `bt=` (R3), is never in this body: it rides the record's `0xB6` trailer, and
//!   a reader that asks for it gets it from the broker's client beside the body
//!   (astream-broker's `Client::broker_times` and `fetch_stamped`).
//!
//! The view reads every `ack` and `expired` record the bridges write on an `in` lane. It
//! ignores `from=` (a node's attested session), `text=` (the pct-encoded words aterm always
//! appends), `dl=` and `via=` on an `ack`, and every key it does not know, in any order, as
//! aterm-link's own total decoder ignores what it does not know. The line ends at the first
//! `\n`; what follows is a `len=` raw tail, which no receipt has. It refuses a body with no
//! `v=1` or another version, no `re=` (an `ack` posted without one settles nothing), an
//! `ack` whose `verdict=` is not one of the three words, an `expired` without a `dl=`, a
//! malformed number, and a field it reads given twice. It never panics.
//!
//! Another face's `ack` is not a receipt, and this view is not for it: the halt answer a
//! node writes on `/f/<F>/pub/<node>/node/ack` (`v=1 t=<ms> re=<halt> state=held|ready`,
//! §5.3) and a barrier answer on `pub/…/ack/<B>` (§5.4). The body alone does not tell them
//! from an `in`-lane `ack` (the halt answer reads as one with no verdict), so the caller
//! takes the kind from an `in` subject.
//!
//! The writers it reads, byte for byte (`what_aterm_and_asb_write_is_this_view`):
//!
//! ```text
//! asb ack                 v=1 t=<ms> re=<off> verdict=<word>                 (V1Receipt::encode)
//! aterm, on `inbox seen`  v=1 t=<ms> from=<sid> re=<off> verdict=<word> text=marked%20<word>%20by%20the%20recipient
//! aterm, a posted `ack`   v=1 t=<ms> from=<sid> [via=<chain>] re=<off> [dl=<ms>] text=<pct>
//! aterm, a deadline       v=1 t=<ms> re=<off> dl=<ms> text=no%20reply%20within%20<span>
//! ```
//!
//! aterm keeps its own lossless decoder (`aterm-link`'s `Body::decode`, which carries what
//! this view ignores), and its tests decode the bytes its bridge writes with this view.
//!
//! ## What nothing writes: [`FabricReceipt`]
//!
//! ```text
//! ack re=<off> verdict=handled|refused|deferred bt=<ms>
//! expired re=<off> dl=<ms> bt=<ms>
//! ```
//!
//! A header word, an ABSOLUTE `dl=`, and a broker time `bt=` in the body, where no broker
//! writes one (a broker's `bt=` rides the record's trailer, above). No
//! writer emits this grammar, and [`FabricReceipt::decode`] refuses every receipt on the
//! bus: the first token of each is `v=1`, which it does not read. (Its `v=1` arm read only
//! the `state=` spelling `asb ack` retired, and took that body's `t=`, the sender's clock,
//! for `bt=`, which R3 says it is not; it is gone.) No writer should be pointed at this
//! grammar as if it were the bus's.
//!
//! It stays because its kernels are proved and exercised: [`deadline_elapsed`] and
//! [`monotone_clock_tick`] are Clean-origin, and `verify.clean-origin-tla-protocols`
//! exercises them beside [`FabricReceipt::new_expired`], [`FabricReceipt::tick_clock`]
//! and an encoded [`FabricReceipt::Ack`].
//!
//! ## Formal Verification (Embedded Clean Island + TLA+ Specification)
//!
//! The `clean { ... }` block below embeds the TLA+ state machine
//! `Astream.Wire.TlaFabricReceipts` and proves in the Clean CIC kernel:
//! 1. `spec_satisfies_receipt_safety`:
//!    `(Spec dl t0) ⊨ □ (Lift ReceiptSafetyInv)` — across all reachable behaviors,
//!    a pending request transitions at most once to either `Acked` (with a valid
//!    non-zero verdict) or `Expired` (only when `dlMs <= btMs <= nowMs`), and
//!    terminal states are mutually exclusive and immutable under clock ticks.
//! 2. `deadline_elapsed`: kernel-certified two-language contract (`clean-kernel-defeq`)
//!    proving `dl_ms <= bt_ms` matches `deadline_elapsed_isl`.
//!
//! WHAT THE MODEL DOES NOT COVER: the bus's deadlines. It judges one request whose deadline
//! is an absolute `dlMs` on the same monotone clock that stamps `btMs`. On the bus the
//! deadline is a relative `dl=` that the asker's bridge turns into an instant on its own
//! clock, and no record carries that instant. No receipt's body carries a `bt=`, and the
//! trailer's (R3), which says when the broker appended the record, reaches neither this
//! model nor this module. So neither the instant nor the check that a recorded `expired`
//! came after it is anything they see. The asker-judged deadline is the bridge's
//! (aterm-link's deadline sweep, and its tests).

use crate::Offset;
use core::fmt;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "receipt_island.rs"]
mod receipt_island;
#[cfg(not(clean_islands))]
pub use crate::twins::monotone_clock_tick;
#[cfg(clean_islands)]
pub use receipt_island::monotone_clock_tick;

contract_fn! {
    /// Kernel-certified deadline-elapsed check (`dl_ms <= bt_ms`), backed by the
    /// Clean-origin [`monotone_clock_tick`] (`max(bt_ms, dl_ms) == bt_ms`).
    #[must_use]
    pub const fn deadline_elapsed(dl_ms: u64, bt_ms: u64) -> bool
    clauses [ensures result == (dl_ms <= bt_ms)]
    {
        dl_ms <= bt_ms
    }
}

/// The three disposition verdicts of a fabric `ack` receipt (`REQUIREMENTS` R8).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ReceiptVerdict {
    /// The recipient processed and completed the request.
    Handled,
    /// The recipient explicitly refused the request.
    Refused,
    /// The recipient recorded the request for later execution.
    Deferred,
}

impl ReceiptVerdict {
    /// Every verdict, in wire order: the whole vocabulary [`Self::parse_bytes`] and
    /// [`V1Receipt::decode`] read. A consumer that needs the words spells them from this
    /// array and [`Self::as_str`], never from a list of its own.
    pub const ALL: [Self; 3] = [Self::Handled, Self::Refused, Self::Deferred];

    /// Canonical lowercase wire token (`handled`, `refused`, `deferred`).
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Handled => "handled",
            Self::Refused => "refused",
            Self::Deferred => "deferred",
        }
    }

    /// Parse a canonical verdict byte slice: the [`Self::as_str`] of one of [`Self::ALL`].
    pub const fn parse_bytes(s: &[u8]) -> Result<Self, ReceiptError> {
        let mut rest: &[Self] = &Self::ALL;
        while let &[verdict, ref tail @ ..] = rest {
            if bytes_eq(s, verdict.as_str().as_bytes()) {
                return Ok(verdict);
            }
            rest = tail;
        }
        Err(ReceiptError::InvalidVerdict)
    }

    /// Parse a canonical verdict token.
    pub const fn parse(s: &str) -> Result<Self, ReceiptError> {
        Self::parse_bytes(s.as_bytes())
    }
}

impl fmt::Display for ReceiptVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// Why a fabric receipt or deadline-expiry body failed to parse.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReceiptError {
    /// A [`FabricReceipt`]'s first token was neither `ack` nor `expired`, or the kind a
    /// [`V1Receipt`] was read under (its subject's last segment) was neither.
    UnknownKind,
    /// A required field (`v=`, `re=`, `verdict=`, `dl=`, `bt=`) was missing, or a field
    /// the decoder reads (those and `t=`) was repeated.
    MissingOrDuplicateField(&'static str),
    /// An unknown `key=value` token appeared in a [`FabricReceipt`] body. (A
    /// [`V1Receipt`] ignores one.)
    UnknownField,
    /// A [`V1Receipt`]'s `v=` was not `1`: a reader that does not know a body's version
    /// does not read it.
    UnknownVersion,
    /// A numeric field (`t=`, `re=`, `dl=`, `bt=`) was not a valid unsigned 64-bit integer.
    InvalidNumber(&'static str),
    /// The `verdict=` value was not `handled|refused|deferred`.
    InvalidVerdict,
    /// An `expired` receipt had `bt < dl` (emitted before the deadline elapsed).
    DeadlineNotElapsed { dl_ms: u64, bt_ms: u64 },
}

impl fmt::Display for ReceiptError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownKind => write!(f, "expected an 'ack' or 'expired' receipt"),
            Self::MissingOrDuplicateField(k) => {
                write!(f, "missing or duplicate receipt field '{k}'")
            }
            Self::UnknownField => write!(f, "unknown field in receipt body"),
            Self::UnknownVersion => write!(f, "receipt body version is not v=1"),
            Self::InvalidNumber(k) => write!(f, "invalid u64 in receipt field '{k}'"),
            Self::InvalidVerdict => {
                write!(
                    f,
                    "invalid receipt verdict (expected handled|refused|deferred)"
                )
            }
            Self::DeadlineNotElapsed { dl_ms, bt_ms } => write!(
                f,
                "expired receipt timestamp bt={bt_ms} is before deadline dl={dl_ms}"
            ),
        }
    }
}

impl std::error::Error for ReceiptError {}

/// The header-first receipt grammar that NO WRITER EMITS (the module doc says why it
/// stays). The receipts on the bus are [`V1Receipt`]s.
#[derive(Debug, Clone, Eq)]
pub enum FabricReceipt {
    /// `ack re=<off> verdict=handled|refused|deferred bt=<ms>`
    Ack {
        /// Log offset of the message being acknowledged.
        re: Offset,
        /// Disposition verdict (`handled`, `refused`, or `deferred`).
        verdict: ReceiptVerdict,
        /// Broker/bridge timestamp in unix milliseconds.
        bt_ms: u64,
    },
    /// `expired re=<off> dl=<ms> bt=<ms>`
    Expired {
        /// Log offset of the message whose deadline elapsed without an answer/report/ack.
        re: Offset,
        /// The original deadline in unix milliseconds.
        dl_ms: u64,
        /// Broker/bridge timestamp in unix milliseconds when expiry was recorded (`bt_ms >= dl_ms`).
        bt_ms: u64,
    },
}

impl PartialEq for FabricReceipt {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Self::Ack {
                    re: r1,
                    verdict: v1,
                    bt_ms: b1,
                },
                Self::Ack {
                    re: r2,
                    verdict: v2,
                    bt_ms: b2,
                },
            ) => r1.0 == r2.0 && *v1 == *v2 && *b1 == *b2,
            (
                Self::Expired {
                    re: r1,
                    dl_ms: d1,
                    bt_ms: b1,
                },
                Self::Expired {
                    re: r2,
                    dl_ms: d2,
                    bt_ms: b2,
                },
            ) => r1.0 == r2.0 && *d1 == *d2 && *b1 == *b2,
            (Self::Ack { .. }, Self::Expired { .. }) | (Self::Expired { .. }, Self::Ack { .. }) => {
                false
            }
        }
    }
}

/// Whether `a` and `b` are the same bytes.
const fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    let (mut a, mut b) = (a, b);
    loop {
        match (a, b) {
            ([], []) => return true,
            (&[x, ref a_tail @ ..], &[y, ref b_tail @ ..]) if x == y => {
                a = a_tail;
                b = b_tail;
            }
            _ => return false,
        }
    }
}

const fn decode_decimal_digit(b: u8) -> Option<u64> {
    if b >= b'0' && b <= b'9' {
        Some((b - b'0') as u64)
    } else {
        None
    }
}

const fn is_all_crlf(bytes: &[u8]) -> bool {
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if b != b'\r' && b != b'\n' {
            return false;
        }
        rest = tail;
    }
    true
}

const fn parse_u64_space_token<'a>(
    bytes: &'a [u8],
    field: &'static str,
) -> Result<(u64, Option<&'a [u8]>), ReceiptError> {
    let mut rest = bytes;
    let mut acc = 0u64;
    let mut has_digit = false;
    while let &[b, ref tail @ ..] = rest {
        if b == b' ' {
            if !has_digit {
                return Err(ReceiptError::InvalidNumber(field));
            }
            return Ok((acc, Some(tail)));
        }
        if b == b'\r' || b == b'\n' {
            if !has_digit || !is_all_crlf(tail) {
                return Err(ReceiptError::InvalidNumber(field));
            }
            return Ok((acc, None));
        }
        let Some(digit) = decode_decimal_digit(b) else {
            return Err(ReceiptError::InvalidNumber(field));
        };
        let Some(mul) = acc.checked_mul(10) else {
            return Err(ReceiptError::InvalidNumber(field));
        };
        let Some(next) = mul.checked_add(digit) else {
            return Err(ReceiptError::InvalidNumber(field));
        };
        acc = next;
        has_digit = true;
        rest = tail;
    }
    if !has_digit {
        return Err(ReceiptError::InvalidNumber(field));
    }
    Ok((acc, None))
}

const fn parse_verdict_space_token(
    bytes: &[u8],
) -> Result<(ReceiptVerdict, Option<&[u8]>), ReceiptError> {
    match bytes {
        b"handled" => Ok((ReceiptVerdict::Handled, None)),
        &[b'h', b'a', b'n', b'd', b'l', b'e', b'd', b' ', ref tail @ ..] => {
            Ok((ReceiptVerdict::Handled, Some(tail)))
        }
        &[b'h', b'a', b'n', b'd', b'l', b'e', b'd', b'\r' | b'\n', ref tail @ ..]
            if is_all_crlf(tail) =>
        {
            Ok((ReceiptVerdict::Handled, None))
        }
        b"refused" => Ok((ReceiptVerdict::Refused, None)),
        &[b'r', b'e', b'f', b'u', b's', b'e', b'd', b' ', ref tail @ ..] => {
            Ok((ReceiptVerdict::Refused, Some(tail)))
        }
        &[b'r', b'e', b'f', b'u', b's', b'e', b'd', b'\r' | b'\n', ref tail @ ..]
            if is_all_crlf(tail) =>
        {
            Ok((ReceiptVerdict::Refused, None))
        }
        b"deferred" => Ok((ReceiptVerdict::Deferred, None)),
        &[b'd', b'e', b'f', b'e', b'r', b'r', b'e', b'd', b' ', ref tail @ ..] => {
            Ok((ReceiptVerdict::Deferred, Some(tail)))
        }
        &[b'd', b'e', b'f', b'e', b'r', b'r', b'e', b'd', b'\r' | b'\n', ref tail @ ..]
            if is_all_crlf(tail) =>
        {
            Ok((ReceiptVerdict::Deferred, None))
        }
        _ => Err(ReceiptError::InvalidVerdict),
    }
}

#[derive(Clone, Copy)]
enum ReceiptHeaderKind {
    Ack,
    Expired,
}

#[derive(Clone, Copy)]
enum AckField<'a> {
    Re(u64, Option<&'a [u8]>),
    Verdict(ReceiptVerdict, Option<&'a [u8]>),
    Bt(u64, Option<&'a [u8]>),
}

const fn parse_ack_field(rem: &[u8]) -> Result<AckField<'_>, ReceiptError> {
    match *rem {
        [b'r', b'e', b'=', ref v @ ..] => match parse_u64_space_token(v, "re") {
            Ok((val, next)) => Ok(AckField::Re(val, next)),
            Err(e) => Err(e),
        },
        [b'v', b'e', b'r', b'd', b'i', b'c', b't', b'=', ref v @ ..] => {
            match parse_verdict_space_token(v) {
                Ok((val, next)) => Ok(AckField::Verdict(val, next)),
                Err(e) => Err(e),
            }
        }
        [b'b', b't', b'=', ref v @ ..] => match parse_u64_space_token(v, "bt") {
            Ok((val, next)) => Ok(AckField::Bt(val, next)),
            Err(e) => Err(e),
        },
        _ => Err(ReceiptError::UnknownField),
    }
}

#[derive(Clone, Copy)]
enum ExpiredField<'a> {
    Re(u64, Option<&'a [u8]>),
    Dl(u64, Option<&'a [u8]>),
    Bt(u64, Option<&'a [u8]>),
}

const fn parse_expired_field(rem: &[u8]) -> Result<ExpiredField<'_>, ReceiptError> {
    match *rem {
        [b'r', b'e', b'=', ref v @ ..] => match parse_u64_space_token(v, "re") {
            Ok((val, next)) => Ok(ExpiredField::Re(val, next)),
            Err(e) => Err(e),
        },
        [b'd', b'l', b'=', ref v @ ..] => match parse_u64_space_token(v, "dl") {
            Ok((val, next)) => Ok(ExpiredField::Dl(val, next)),
            Err(e) => Err(e),
        },
        [b'b', b't', b'=', ref v @ ..] => match parse_u64_space_token(v, "bt") {
            Ok((val, next)) => Ok(ExpiredField::Bt(val, next)),
            Err(e) => Err(e),
        },
        _ => Err(ReceiptError::UnknownField),
    }
}

impl FabricReceipt {
    /// Advance a bridge/broker monotone clock `now_ms` by `sample_ms`
    /// (`max(now_ms, sample_ms)`), backed directly by the Clean-origin
    /// [`monotone_clock_tick`] function used in `TlaFabricReceipts.TickClock`.
    #[must_use]
    pub const fn tick_clock(now_ms: u64, sample_ms: u64) -> u64 {
        if now_ms < sample_ms {
            sample_ms
        } else {
            now_ms
        }
    }

    /// Construct a validated `expired` receipt, checking that `bt_ms >= dl_ms`
    /// ([`deadline_elapsed`]).
    pub const fn new_expired(re: Offset, dl_ms: u64, bt_ms: u64) -> Result<Self, ReceiptError> {
        if dl_ms > bt_ms {
            return Err(ReceiptError::DeadlineNotElapsed { dl_ms, bt_ms });
        }
        Ok(Self::Expired { re, dl_ms, bt_ms })
    }

    /// Referenced message offset (`re=<off>`).
    #[must_use]
    pub const fn re(&self) -> Offset {
        match self {
            Self::Ack { re, .. } | Self::Expired { re, .. } => *re,
        }
    }

    /// Timestamp (`bt=<ms>`) carried by the receipt.
    #[must_use]
    pub const fn bt_ms(&self) -> u64 {
        match self {
            Self::Ack { bt_ms, .. } | Self::Expired { bt_ms, .. } => *bt_ms,
        }
    }

    /// Format into the header-first grammar (which no writer emits).
    #[must_use]
    pub fn encode(&self) -> String {
        match self {
            Self::Ack { re, verdict, bt_ms } => {
                format!("ack re={} verdict={} bt={bt_ms}", re.0, verdict.as_str())
            }
            Self::Expired { re, dl_ms, bt_ms } => {
                format!("expired re={} dl={dl_ms} bt={bt_ms}", re.0)
            }
        }
    }

    /// Decode a header-first `ack re=…` or `expired re=…` line from a byte slice. A `v=1`
    /// body, which every receipt on the bus is, is [`ReceiptError::UnknownKind`] here:
    /// read it with [`V1Receipt::decode`].
    pub const fn decode_bytes(input: &[u8]) -> Result<Self, ReceiptError> {
        let (kind, mut rest_opt) = match input {
            b"ack" => (ReceiptHeaderKind::Ack, None),
            &[b'a', b'c', b'k', b' ', ref tail @ ..] => (ReceiptHeaderKind::Ack, Some(tail)),
            b"expired" => (ReceiptHeaderKind::Expired, None),
            &[b'e', b'x', b'p', b'i', b'r', b'e', b'd', b' ', ref tail @ ..] => {
                (ReceiptHeaderKind::Expired, Some(tail))
            }
            _ => return Err(ReceiptError::UnknownKind),
        };
        match kind {
            ReceiptHeaderKind::Ack => {
                let mut re: Option<Offset> = None;
                let mut verdict: Option<ReceiptVerdict> = None;
                let mut bt_ms: Option<u64> = None;
                while let Some(rem) = rest_opt {
                    match parse_ack_field(rem) {
                        Ok(AckField::Re(val, next_rest)) => {
                            if re.is_some() {
                                return Err(ReceiptError::MissingOrDuplicateField("re"));
                            }
                            re = Some(Offset(val));
                            rest_opt = next_rest;
                        }
                        Ok(AckField::Verdict(val, next_rest)) => {
                            if verdict.is_some() {
                                return Err(ReceiptError::MissingOrDuplicateField("verdict"));
                            }
                            verdict = Some(val);
                            rest_opt = next_rest;
                        }
                        Ok(AckField::Bt(val, next_rest)) => {
                            if bt_ms.is_some() {
                                return Err(ReceiptError::MissingOrDuplicateField("bt"));
                            }
                            bt_ms = Some(val);
                            rest_opt = next_rest;
                        }
                        Err(e) => return Err(e),
                    }
                }
                let Some(re) = re else {
                    return Err(ReceiptError::MissingOrDuplicateField("re"));
                };
                let Some(verdict) = verdict else {
                    return Err(ReceiptError::MissingOrDuplicateField("verdict"));
                };
                let Some(bt_ms) = bt_ms else {
                    return Err(ReceiptError::MissingOrDuplicateField("bt"));
                };
                Ok(Self::Ack { re, verdict, bt_ms })
            }
            ReceiptHeaderKind::Expired => {
                let mut re: Option<Offset> = None;
                let mut dl_ms: Option<u64> = None;
                let mut bt_ms: Option<u64> = None;
                while let Some(rem) = rest_opt {
                    match parse_expired_field(rem) {
                        Ok(ExpiredField::Re(val, next_rest)) => {
                            if re.is_some() {
                                return Err(ReceiptError::MissingOrDuplicateField("re"));
                            }
                            re = Some(Offset(val));
                            rest_opt = next_rest;
                        }
                        Ok(ExpiredField::Dl(val, next_rest)) => {
                            if dl_ms.is_some() {
                                return Err(ReceiptError::MissingOrDuplicateField("dl"));
                            }
                            dl_ms = Some(val);
                            rest_opt = next_rest;
                        }
                        Ok(ExpiredField::Bt(val, next_rest)) => {
                            if bt_ms.is_some() {
                                return Err(ReceiptError::MissingOrDuplicateField("bt"));
                            }
                            bt_ms = Some(val);
                            rest_opt = next_rest;
                        }
                        Err(e) => return Err(e),
                    }
                }
                let Some(re) = re else {
                    return Err(ReceiptError::MissingOrDuplicateField("re"));
                };
                let Some(dl_ms) = dl_ms else {
                    return Err(ReceiptError::MissingOrDuplicateField("dl"));
                };
                let Some(bt_ms) = bt_ms else {
                    return Err(ReceiptError::MissingOrDuplicateField("bt"));
                };
                Self::new_expired(re, dl_ms, bt_ms)
            }
        }
    }

    /// Decode a header-first `ack re=…` or `expired re=…` line ([`Self::decode_bytes`]).
    pub const fn decode(input: &str) -> Result<Self, ReceiptError> {
        Self::decode_bytes(input.as_bytes())
    }
}

impl fmt::Display for FabricReceipt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.encode())
    }
}

/// A receipt as the bridges write it: a §4.1 `v=1` body on an `in` lane, read under the
/// kind its subject's last segment names. The module doc has the grammar, what the view
/// ignores and refuses, and the writers it reads.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum V1Receipt {
    /// Kind `ack`: `v=1 t=<ms> re=<off> [verdict=handled|refused|deferred]`.
    Ack {
        /// Log offset of the `ask` or `task` the recipient settled.
        re: Offset,
        /// What the recipient did with it: `Some` on the receipt `inbox seen` and
        /// `asb ack` write, `None` on a session's own `post kind=ack`, which settles the
        /// ask with words (`text=`) and no verdict.
        verdict: Option<ReceiptVerdict>,
        /// The sender's wall clock (`t=`), informational, never a broker time; `None` when
        /// the body has no `t=`.
        sender_t_ms: Option<u64>,
    },
    /// Kind `expired`: `v=1 t=<ms> re=<off> dl=<ms>`.
    Expired {
        /// Log offset of the `ask` or `task` whose deadline passed unanswered.
        re: Offset,
        /// The deadline the ask carried, RELATIVE: a span in ms the asker's bridge counted
        /// on its own clock, not an instant.
        dl_ms: u64,
        /// The sender's wall clock (`t=`), informational, never a broker time; `None` when
        /// the body has no `t=`.
        sender_t_ms: Option<u64>,
    },
}

/// The rest of a §4.1 line after the value at the front of `bytes`: the bytes after the
/// next ` `, or `None` at the line's end (the end of the bytes, or a `\n`).
const fn after_value(bytes: &[u8]) -> Option<&[u8]> {
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        if b == b' ' {
            return Some(tail);
        }
        if b == b'\n' {
            return None;
        }
        rest = tail;
    }
    None
}

/// Whether the value at the front of `bytes` is exactly `word`: `Some` of what follows it
/// (as [`after_value`] answers), `None` when the value is anything else.
const fn whole_value<'a>(bytes: &'a [u8], word: &[u8]) -> Option<Option<&'a [u8]>> {
    let mut rest = bytes;
    let mut want = word;
    while let &[w, ref want_tail @ ..] = want {
        match rest {
            &[b, ref tail @ ..] if b == w => {
                rest = tail;
                want = want_tail;
            }
            _ => return None,
        }
    }
    match rest {
        [] | [b'\n', ..] => Some(None),
        &[b' ', ref tail @ ..] => Some(Some(tail)),
        _ => None,
    }
}

/// The decimal `u64` at the front of `bytes`, and what follows it (as [`after_value`]
/// answers). Digits only: no sign, no space, at least one, no overflow.
const fn view_u64<'a>(
    bytes: &'a [u8],
    field: &'static str,
) -> Result<(u64, Option<&'a [u8]>), ReceiptError> {
    let mut rest = bytes;
    let mut acc = 0u64;
    let mut has_digit = false;
    while let &[b, ref tail @ ..] = rest {
        if b == b' ' || b == b'\n' {
            if !has_digit {
                return Err(ReceiptError::InvalidNumber(field));
            }
            return Ok((acc, if b == b' ' { Some(tail) } else { None }));
        }
        let Some(digit) = decode_decimal_digit(b) else {
            return Err(ReceiptError::InvalidNumber(field));
        };
        let Some(mul) = acc.checked_mul(10) else {
            return Err(ReceiptError::InvalidNumber(field));
        };
        let Some(next) = mul.checked_add(digit) else {
            return Err(ReceiptError::InvalidNumber(field));
        };
        acc = next;
        has_digit = true;
        rest = tail;
    }
    if !has_digit {
        return Err(ReceiptError::InvalidNumber(field));
    }
    Ok((acc, None))
}

/// The verdict word at the front of `bytes`, one of [`ReceiptVerdict::ALL`], and what
/// follows it.
const fn view_verdict(bytes: &[u8]) -> Result<(ReceiptVerdict, Option<&[u8]>), ReceiptError> {
    let mut rest: &[ReceiptVerdict] = &ReceiptVerdict::ALL;
    while let &[verdict, ref tail @ ..] = rest {
        if let Some(next) = whole_value(bytes, verdict.as_str().as_bytes()) {
            return Ok((verdict, next));
        }
        rest = tail;
    }
    Err(ReceiptError::InvalidVerdict)
}

#[derive(Clone, Copy)]
enum V1Key<'a> {
    End,
    Skip(Option<&'a [u8]>),
    V(&'a [u8]),
    T(&'a [u8]),
    Re(&'a [u8]),
    Verdict(&'a [u8]),
    Dl(&'a [u8]),
}

const fn classify_v1_key(rem: &[u8], ack: bool) -> V1Key<'_> {
    let &[b0, ref r1 @ ..] = rem else {
        return V1Key::End;
    };
    match b0 {
        b'\n' => V1Key::End,
        b' ' => V1Key::Skip(Some(r1)),
        b'v' => {
            if let &[b'=', ref val @ ..] = r1 {
                V1Key::V(val)
            } else if let &[b'e', b'r', b'd', b'i', b'c', b't', b'=', ref val @ ..] = r1 {
                if ack {
                    V1Key::Verdict(val)
                } else {
                    V1Key::Skip(after_value(rem))
                }
            } else {
                V1Key::Skip(after_value(rem))
            }
        }
        b't' => {
            if let &[b'=', ref val @ ..] = r1 {
                V1Key::T(val)
            } else {
                V1Key::Skip(after_value(rem))
            }
        }
        b'r' => {
            if let &[b'e', b'=', ref val @ ..] = r1 {
                V1Key::Re(val)
            } else {
                V1Key::Skip(after_value(rem))
            }
        }
        b'd' => {
            if let &[b'l', b'=', ref val @ ..] = r1 {
                if !ack {
                    V1Key::Dl(val)
                } else {
                    V1Key::Skip(after_value(rem))
                }
            } else {
                V1Key::Skip(after_value(rem))
            }
        }
        _ => V1Key::Skip(after_value(rem)),
    }
}

impl V1Receipt {
    /// Read a §4.1 receipt `body` under `kind`, the last segment of its subject (`ack` or
    /// `expired`; anything else is [`ReceiptError::UnknownKind`]).
    ///
    /// It needs `v=1` and `re=`, and `dl=` on an `expired`; it reads an `ack`'s `verdict=`
    /// when there is one, and keeps `t=` as [`Self::sender_t_ms`]. Every other key
    /// (`from=`, `text=`, one it does not know, and the other kind's field) is skipped
    /// unread, in any order, and the line ends at the first `\n`. `kind` must come from an
    /// `in` subject: another face's `ack` (a node's halt answer) is not a receipt.
    ///
    /// # Errors
    ///
    /// [`ReceiptError::UnknownKind`] for another kind, [`ReceiptError::UnknownVersion`] for a
    /// `v=` other than `1`, [`ReceiptError::MissingOrDuplicateField`] for a required field
    /// that is absent or a field it reads given twice, [`ReceiptError::InvalidNumber`] for
    /// a malformed `t=`, `re=` or `dl=`, and [`ReceiptError::InvalidVerdict`] for a word
    /// outside the three.
    pub const fn decode(kind: &str, body: &[u8]) -> Result<Self, ReceiptError> {
        let ack = match kind.as_bytes() {
            b"ack" => true,
            b"expired" => false,
            _ => return Err(ReceiptError::UnknownKind),
        };
        let mut v1 = false;
        let mut sender_t_ms: Option<u64> = None;
        let mut re: Option<Offset> = None;
        let mut verdict: Option<ReceiptVerdict> = None;
        let mut dl_ms: Option<u64> = None;
        let mut rest = Some(body);
        while let Some(rem) = rest {
            rest = match classify_v1_key(rem, ack) {
                V1Key::End => None,
                V1Key::Skip(next) => next,
                V1Key::V(val) => {
                    if v1 {
                        return Err(ReceiptError::MissingOrDuplicateField("v"));
                    }
                    let Some(next) = whole_value(val, b"1") else {
                        return Err(ReceiptError::UnknownVersion);
                    };
                    v1 = true;
                    next
                }
                V1Key::T(val) => {
                    if sender_t_ms.is_some() {
                        return Err(ReceiptError::MissingOrDuplicateField("t"));
                    }
                    match view_u64(val, "t") {
                        Ok((t, next)) => {
                            sender_t_ms = Some(t);
                            next
                        }
                        Err(e) => return Err(e),
                    }
                }
                V1Key::Re(val) => {
                    if re.is_some() {
                        return Err(ReceiptError::MissingOrDuplicateField("re"));
                    }
                    match view_u64(val, "re") {
                        Ok((off, next)) => {
                            re = Some(Offset(off));
                            next
                        }
                        Err(e) => return Err(e),
                    }
                }
                V1Key::Verdict(val) => {
                    if verdict.is_some() {
                        return Err(ReceiptError::MissingOrDuplicateField("verdict"));
                    }
                    match view_verdict(val) {
                        Ok((word, next)) => {
                            verdict = Some(word);
                            next
                        }
                        Err(e) => return Err(e),
                    }
                }
                V1Key::Dl(val) => {
                    if dl_ms.is_some() {
                        return Err(ReceiptError::MissingOrDuplicateField("dl"));
                    }
                    match view_u64(val, "dl") {
                        Ok((dl, next)) => {
                            dl_ms = Some(dl);
                            next
                        }
                        Err(e) => return Err(e),
                    }
                }
            };
        }
        if !v1 {
            return Err(ReceiptError::MissingOrDuplicateField("v"));
        }
        let Some(re) = re else {
            return Err(ReceiptError::MissingOrDuplicateField("re"));
        };
        if ack {
            Ok(Self::Ack {
                re,
                verdict,
                sender_t_ms,
            })
        } else {
            let Some(dl_ms) = dl_ms else {
                return Err(ReceiptError::MissingOrDuplicateField("dl"));
            };
            Ok(Self::Expired {
                re,
                dl_ms,
                sender_t_ms,
            })
        }
    }

    /// The bare line, every field the view reads and nothing else:
    /// `v=1 t=<ms> re=<off> verdict=<word>` for an `ack` (what `asb ack` writes), with no
    /// `verdict=` when there is none, and `v=1 t=<ms> re=<off> dl=<ms>` for an `expired`,
    /// with no `t=` when there is no [`Self::sender_t_ms`]. [`Self::decode`] under
    /// [`Self::kind`] gives `self` back.
    #[must_use]
    pub fn encode(&self) -> String {
        let t = match self.sender_t_ms() {
            Some(t) => format!(" t={t}"),
            None => String::new(),
        };
        match self {
            Self::Ack { re, verdict, .. } => match verdict {
                Some(verdict) => format!("v=1{t} re={} verdict={}", re.0, verdict.as_str()),
                None => format!("v=1{t} re={}", re.0),
            },
            Self::Expired { re, dl_ms, .. } => format!("v=1{t} re={} dl={dl_ms}", re.0),
        }
    }

    /// The subject's last segment this receipt is published under: `ack` or `expired`.
    #[must_use]
    pub const fn kind(&self) -> &'static str {
        match self {
            Self::Ack { .. } => "ack",
            Self::Expired { .. } => "expired",
        }
    }

    /// The offset of the `ask` or `task` the receipt settles (`re=`).
    #[must_use]
    pub const fn re(&self) -> Offset {
        match self {
            Self::Ack { re, .. } | Self::Expired { re, .. } => *re,
        }
    }

    /// The sender's wall clock (`t=`), informational. A broker's `bt=` (R3) is never in the
    /// body this reads: it rides the record's trailer.
    #[must_use]
    pub const fn sender_t_ms(&self) -> Option<u64> {
        match self {
            Self::Ack { sender_t_ms, .. } | Self::Expired { sender_t_ms, .. } => *sender_t_ms,
        }
    }
}

impl fmt::Display for V1Receipt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.encode())
    }
}

/// State reported on a node's halt acknowledgment face (`/f/<F>/pub/<node>/node/ack`,
/// `DESIGN-aterm-fabric.md` §5.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NodeAckState {
    /// Every live session on the node has been placed under the fleet drive hold.
    Held,
    /// The fleet drive hold has been lifted across the node's sessions.
    Ready,
}

impl NodeAckState {
    /// Closed vocabulary of node halt-ack states (`held`, `ready`).
    pub const ALL: [Self; 2] = [Self::Held, Self::Ready];

    /// Canonical lowercase wire token (`held`, `ready`).
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Held => "held",
            Self::Ready => "ready",
        }
    }

    /// Parse a canonical node-ack state byte slice.
    pub const fn parse_bytes(s: &[u8]) -> Result<Self, ReceiptError> {
        let mut rest: &[Self] = &Self::ALL;
        while let &[st, ref tail @ ..] = rest {
            if bytes_eq(s, st.as_str().as_bytes()) {
                return Ok(st);
            }
            rest = tail;
        }
        Err(ReceiptError::InvalidVerdict)
    }

    /// Parse a canonical node-ack state token.
    pub const fn parse(s: &str) -> Result<Self, ReceiptError> {
        Self::parse_bytes(s.as_bytes())
    }
}

impl fmt::Display for NodeAckState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

const fn view_node_ack_state(bytes: &[u8]) -> Result<(NodeAckState, Option<&[u8]>), ReceiptError> {
    let mut rest: &[NodeAckState] = &NodeAckState::ALL;
    while let &[st, ref tail @ ..] = rest {
        if let Some(next) = whole_value(bytes, st.as_str().as_bytes()) {
            return Ok((st, next));
        }
        rest = tail;
    }
    Err(ReceiptError::InvalidVerdict)
}

/// View of a node's retained halt answer on `/f/<F>/pub/<node>/node/ack`
/// (`v=1 t=<ms> re=<halt-offset> state=held|ready`, `DESIGN-aterm-fabric.md` §5.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct V1NodeAck {
    /// Offset of the newest `/f/<F>/fleet/<h>/halt` transition this node reached (`re=`).
    pub re: Offset,
    /// Endpoint hold state reached for `re` (`held` or `ready`).
    pub state: NodeAckState,
    /// Sender wall clock (`t=`), informational; `None` when omitted.
    pub sender_t_ms: Option<u64>,
}

#[derive(Clone, Copy)]
enum StateAckKey<'a> {
    End,
    Skip(Option<&'a [u8]>),
    V(&'a [u8]),
    T(&'a [u8]),
    Re(&'a [u8]),
    State(&'a [u8]),
}

const fn classify_state_ack_key(rem: &[u8]) -> StateAckKey<'_> {
    let &[b0, ref r1 @ ..] = rem else {
        return StateAckKey::End;
    };
    match b0 {
        b'\n' => StateAckKey::End,
        b' ' => StateAckKey::Skip(Some(r1)),
        b'v' => {
            if let &[b'=', ref val @ ..] = r1 {
                StateAckKey::V(val)
            } else {
                StateAckKey::Skip(after_value(rem))
            }
        }
        b't' => {
            if let &[b'=', ref val @ ..] = r1 {
                StateAckKey::T(val)
            } else {
                StateAckKey::Skip(after_value(rem))
            }
        }
        b'r' => {
            if let &[b'e', b'=', ref val @ ..] = r1 {
                StateAckKey::Re(val)
            } else {
                StateAckKey::Skip(after_value(rem))
            }
        }
        b's' => {
            if let &[b't', b'a', b't', b'e', b'=', ref val @ ..] = r1 {
                StateAckKey::State(val)
            } else {
                StateAckKey::Skip(after_value(rem))
            }
        }
        _ => StateAckKey::Skip(after_value(rem)),
    }
}

impl V1NodeAck {
    /// Decode a `/f/<F>/pub/<node>/node/ack` body (`v=1 [t=<ms>] re=<off> state=held|ready`).
    pub const fn decode(body: &[u8]) -> Result<Self, ReceiptError> {
        let mut v1 = false;
        let mut sender_t_ms: Option<u64> = None;
        let mut re: Option<Offset> = None;
        let mut state: Option<NodeAckState> = None;
        let mut rest = Some(body);
        while let Some(rem) = rest {
            rest = match classify_state_ack_key(rem) {
                StateAckKey::End => None,
                StateAckKey::Skip(next) => next,
                StateAckKey::V(val) => {
                    if v1 {
                        return Err(ReceiptError::MissingOrDuplicateField("v"));
                    }
                    let Some(next) = whole_value(val, b"1") else {
                        return Err(ReceiptError::UnknownVersion);
                    };
                    v1 = true;
                    next
                }
                StateAckKey::T(val) => {
                    if sender_t_ms.is_some() {
                        return Err(ReceiptError::MissingOrDuplicateField("t"));
                    }
                    match view_u64(val, "t") {
                        Ok((t, next)) => {
                            sender_t_ms = Some(t);
                            next
                        }
                        Err(e) => return Err(e),
                    }
                }
                StateAckKey::Re(val) => {
                    if re.is_some() {
                        return Err(ReceiptError::MissingOrDuplicateField("re"));
                    }
                    match view_u64(val, "re") {
                        Ok((off, next)) => {
                            re = Some(Offset(off));
                            next
                        }
                        Err(e) => return Err(e),
                    }
                }
                StateAckKey::State(val) => {
                    if state.is_some() {
                        return Err(ReceiptError::MissingOrDuplicateField("state"));
                    }
                    match view_node_ack_state(val) {
                        Ok((st, next)) => {
                            state = Some(st);
                            next
                        }
                        Err(e) => return Err(e),
                    }
                }
            };
        }
        if !v1 {
            return Err(ReceiptError::MissingOrDuplicateField("v"));
        }
        let Some(re) = re else {
            return Err(ReceiptError::MissingOrDuplicateField("re"));
        };
        let Some(state) = state else {
            return Err(ReceiptError::MissingOrDuplicateField("state"));
        };
        Ok(Self {
            re,
            state,
            sender_t_ms,
        })
    }

    /// Encode into canonical `v=1 [t=<ms>] re=<off> state=held|ready` form.
    #[must_use]
    pub fn encode(&self) -> String {
        match self.sender_t_ms {
            Some(t) => format!("v=1 t={t} re={} state={}", self.re.0, self.state.as_str()),
            None => format!("v=1 re={} state={}", self.re.0, self.state.as_str()),
        }
    }

    /// Judge this single-subject node row against `halt_offset` (`DESIGN-aterm-fabric.md` §5.3):
    /// returns `Some(self.state)` iff `self.re == halt_offset`. When `self.re > halt_offset`,
    /// the node overwrote its single row with a later halt transition (so the earlier halt is
    /// unknown, not absent); when `self.re < halt_offset`, the node has not yet acked it.
    #[must_use]
    pub const fn answers_halt_at(&self, halt_offset: Offset) -> Option<NodeAckState> {
        if self.re.0 == halt_offset.0 {
            Some(self.state)
        } else {
            None
        }
    }
}

impl fmt::Display for V1NodeAck {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.encode())
    }
}

/// State reported on a member's barrier answer face (`/f/<F>/pub/<owner>/ack/<B>`,
/// `DESIGN-aterm-fabric.md` §4.2, §5.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BarrierAckState {
    /// Member explicitly consented / reached the barrier (`ready`).
    Ready,
    /// Bridge auto-answered liveness while member was mid-turn (`busy`).
    Busy,
    /// Member explicitly refused the barrier (`refused`).
    Refused,
    /// Bridge auto-answered that the session has exited (`absent`).
    Absent,
    /// Member is held under a fleet halt (`held`).
    Held,
}

impl BarrierAckState {
    /// Closed vocabulary of barrier-ack states (`ready|busy|refused|absent|held`, §4.2).
    pub const ALL: [Self; 5] = [
        Self::Ready,
        Self::Busy,
        Self::Refused,
        Self::Absent,
        Self::Held,
    ];

    /// Canonical lowercase wire token.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Ready => "ready",
            Self::Busy => "busy",
            Self::Refused => "refused",
            Self::Absent => "absent",
            Self::Held => "held",
        }
    }

    /// Whether this state is an automatic bridge liveness echo (`busy` or `absent`) rather
    /// than explicit member consent/refusal (`DESIGN-aterm-fabric.md` §5.4).
    #[must_use]
    pub const fn is_liveness_only(self) -> bool {
        matches!(self, Self::Busy | Self::Absent)
    }

    /// Parse a canonical barrier-ack state byte slice.
    pub const fn parse_bytes(s: &[u8]) -> Result<Self, ReceiptError> {
        let mut rest: &[Self] = &Self::ALL;
        while let &[st, ref tail @ ..] = rest {
            if bytes_eq(s, st.as_str().as_bytes()) {
                return Ok(st);
            }
            rest = tail;
        }
        Err(ReceiptError::InvalidVerdict)
    }

    /// Parse a canonical barrier-ack state token.
    pub const fn parse(s: &str) -> Result<Self, ReceiptError> {
        Self::parse_bytes(s.as_bytes())
    }
}

impl fmt::Display for BarrierAckState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

const fn view_barrier_ack_state(
    bytes: &[u8],
) -> Result<(BarrierAckState, Option<&[u8]>), ReceiptError> {
    let mut rest: &[BarrierAckState] = &BarrierAckState::ALL;
    while let &[st, ref tail @ ..] = rest {
        if let Some(next) = whole_value(bytes, st.as_str().as_bytes()) {
            return Ok((st, next));
        }
        rest = tail;
    }
    Err(ReceiptError::InvalidVerdict)
}

/// View of a member's retained barrier answer on `/f/<F>/pub/<owner>/ack/<B>`
/// (`v=1 [t=<ms>] [re=<B>] state=ready|busy|refused|absent|held [reason=…]`, §4.2, §5.4).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct V1BarrierAck {
    /// Optional explicit `re=<B>` offset in the body (when absent, `<B>` comes from the
    /// subject's trailing segment).
    pub re: Option<Offset>,
    /// Reported barrier state (`ready`, `busy`, `refused`, `absent`, or `held`).
    pub state: BarrierAckState,
    /// Sender wall clock (`t=`), informational; `None` when omitted.
    pub sender_t_ms: Option<u64>,
}

impl V1BarrierAck {
    /// Decode a `/f/<F>/pub/<owner>/ack/<B>` body (`v=1 [t=<ms>] [re=<B>] state=<word>`).
    pub const fn decode(body: &[u8]) -> Result<Self, ReceiptError> {
        let mut v1 = false;
        let mut sender_t_ms: Option<u64> = None;
        let mut re: Option<Offset> = None;
        let mut state: Option<BarrierAckState> = None;
        let mut rest = Some(body);
        while let Some(rem) = rest {
            rest = match classify_state_ack_key(rem) {
                StateAckKey::End => None,
                StateAckKey::Skip(next) => next,
                StateAckKey::V(val) => {
                    if v1 {
                        return Err(ReceiptError::MissingOrDuplicateField("v"));
                    }
                    let Some(next) = whole_value(val, b"1") else {
                        return Err(ReceiptError::UnknownVersion);
                    };
                    v1 = true;
                    next
                }
                StateAckKey::T(val) => {
                    if sender_t_ms.is_some() {
                        return Err(ReceiptError::MissingOrDuplicateField("t"));
                    }
                    match view_u64(val, "t") {
                        Ok((t, next)) => {
                            sender_t_ms = Some(t);
                            next
                        }
                        Err(e) => return Err(e),
                    }
                }
                StateAckKey::Re(val) => {
                    if re.is_some() {
                        return Err(ReceiptError::MissingOrDuplicateField("re"));
                    }
                    match view_u64(val, "re") {
                        Ok((off, next)) => {
                            re = Some(Offset(off));
                            next
                        }
                        Err(e) => return Err(e),
                    }
                }
                StateAckKey::State(val) => {
                    if state.is_some() {
                        return Err(ReceiptError::MissingOrDuplicateField("state"));
                    }
                    match view_barrier_ack_state(val) {
                        Ok((st, next)) => {
                            state = Some(st);
                            next
                        }
                        Err(e) => return Err(e),
                    }
                }
            };
        }
        if !v1 {
            return Err(ReceiptError::MissingOrDuplicateField("v"));
        }
        let Some(state) = state else {
            return Err(ReceiptError::MissingOrDuplicateField("state"));
        };
        Ok(Self {
            re,
            state,
            sender_t_ms,
        })
    }

    /// Encode into canonical `v=1 [t=<ms>] [re=<B>] state=<word>` form.
    #[must_use]
    pub fn encode(&self) -> String {
        let t = match self.sender_t_ms {
            Some(t) => format!(" t={t}"),
            None => String::new(),
        };
        match self.re {
            Some(re) => format!("v=1{t} re={} state={}", re.0, self.state.as_str()),
            None => format!("v=1{t} state={}", self.state.as_str()),
        }
    }

    /// Validate that a `Last{/f/<F>/pub/*/*/ack/<B>}` row at `record_offset` genuinely
    /// answers `barrier_offset` (`DESIGN-aterm-fabric.md` §5.4: discard any pre-published
    /// `ack/<B>` whose own log offset is `< B`, or whose explicit `re=` disagrees with `B`).
    #[must_use]
    pub const fn valid_for_barrier(&self, record_offset: Offset, barrier_offset: Offset) -> bool {
        if record_offset.0 < barrier_offset.0 {
            return false;
        }
        match self.re {
            Some(re) => re.0 == barrier_offset.0,
            None => true,
        }
    }
}

impl fmt::Display for V1BarrierAck {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.encode())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    #[test]
    fn r8_ack_and_expired_grammar_conformance() {
        for (v_str, v_enum) in [
            ("handled", ReceiptVerdict::Handled),
            ("refused", ReceiptVerdict::Refused),
            ("deferred", ReceiptVerdict::Deferred),
        ] {
            let wire = format!("ack re=42 verdict={v_str} bt=1700000000123");
            let decoded = FabricReceipt::decode(&wire).unwrap();
            assert_eq!(
                decoded,
                FabricReceipt::Ack {
                    re: Offset(42),
                    verdict: v_enum,
                    bt_ms: 1_700_000_000_123,
                }
            );
            assert_eq!(decoded.encode(), wire);
            assert_eq!(decoded.re(), Offset(42));
            assert_eq!(decoded.bt_ms(), 1_700_000_000_123);
        }

        let exp_wire = "expired re=99 dl=1700000005000 bt=1700000005000";
        let decoded_exp = FabricReceipt::decode(exp_wire).unwrap();
        assert_eq!(
            decoded_exp,
            FabricReceipt::Expired {
                re: Offset(99),
                dl_ms: 1_700_000_005_000,
                bt_ms: 1_700_000_005_000,
            }
        );
        assert_eq!(decoded_exp.encode(), exp_wire);

        // Premature expiry (`bt < dl`) is rejected by `deadline_elapsed`.
        assert_eq!(
            FabricReceipt::decode("expired re=99 dl=1700000005000 bt=1700000004999"),
            Err(ReceiptError::DeadlineNotElapsed {
                dl_ms: 1_700_000_005_000,
                bt_ms: 1_700_000_004_999,
            })
        );
    }

    #[test]
    fn rejects_malformed_receipts() {
        // Header-first records and CR/LF endings remain valid.
        let valid = ["ack re=1 verdict=handled bt=10", "expired bt=10 re=1 dl=9"];
        for wire in valid {
            let expected = FabricReceipt::decode(wire).unwrap();
            for ending in ["", "\n", "\r\n", "\r\n\r"] {
                let line = format!("{wire}{ending}");
                assert_eq!(FabricReceipt::decode(&line), Ok(expected.clone()));
                assert_eq!(
                    FabricReceipt::decode_bytes(line.as_bytes()),
                    Ok(expected.clone())
                );
            }
        }
        assert_eq!(
            FabricReceipt::decode("unknown re=1"),
            Err(ReceiptError::UnknownKind)
        );
        // The `v=1` arm is retired: the spelling `asb ack` used to write (`state=`) is
        // no header-first record either, and its sender `t=` is no longer read as `bt=`.
        assert_eq!(
            FabricReceipt::decode("v=1 t=10 re=1 state=deferred"),
            Err(ReceiptError::UnknownKind)
        );
        assert_eq!(
            FabricReceipt::decode("ack re=1 verdict=maybe bt=10"),
            Err(ReceiptError::InvalidVerdict)
        );
        assert_eq!(
            FabricReceipt::decode("ack re=1 re=2 verdict=handled bt=10"),
            Err(ReceiptError::MissingOrDuplicateField("re"))
        );
        assert_eq!(
            FabricReceipt::decode("ack re=+1 verdict=handled bt=10"),
            Err(ReceiptError::InvalidNumber("re"))
        );
        // A field separator promises another token; it is not a line ending.
        for wire in valid {
            for ending in [" ", " \r\n"] {
                let malformed = format!("{wire}{ending}");
                assert_eq!(
                    FabricReceipt::decode(&malformed),
                    Err(ReceiptError::UnknownField),
                    "RECEIPT_SPACE_IS_NOT_A_LINE_END: {malformed:?}"
                );
                assert_eq!(
                    FabricReceipt::decode_bytes(malformed.as_bytes()),
                    Err(ReceiptError::UnknownField)
                );
            }
        }
    }

    /// The bytes `asb ack` (asb.rs `cmd_ack`) and aterm's bridge (`aterm-link`'s
    /// `Body::encode`: `from=` on a receipt, a pct-encoded `text=` on both) write.
    const ASB_ACK: &str = "v=1 t=1700000000999 re=7 verdict=handled";
    const ATERM_RECEIPT: &str = "v=1 t=1700000000999 from=s-host re=41 verdict=handled \
                                 text=marked%20handled%20by%20the%20recipient";
    const ATERM_EXPIRED: &str =
        "v=1 t=1700000000999 re=7 dl=240000 text=no%20reply%20within%20240%20s";
    /// A session's own `post to=<asker> kind=ack re=41 text=got it`, as aterm's bridge
    /// publishes it on the asker's `…/ack` lane (`drain_post`): no `verdict=`.
    const ATERM_POSTED_ACK: &str = "v=1 t=1700000000999 from=s-b re=41 text=got%20it";

    /// WHAT THE MODULE DOC SAYS OF THE BUS, PINNED ON THE WRITERS' OWN BYTES. Each of
    /// the four lines decodes under the kind its subject names, field for field: `re=`,
    /// the verdict (none on a session's own posted `ack`) or the RELATIVE `dl=`, and `t=`
    /// as the sender's clock. `asb ack`'s line is exactly what [`V1Receipt::encode`]
    /// writes. [`FabricReceipt`] refuses all four (the header-first grammar is not the
    /// bus's). aterm's own tests decode its bridge's real bytes with this view; these
    /// copies say what the view reads, not that aterm still writes them.
    #[test]
    fn what_aterm_and_asb_write_is_this_view() {
        let asb = V1Receipt::Ack {
            re: Offset(7),
            verdict: Some(ReceiptVerdict::Handled),
            sender_t_ms: Some(1_700_000_000_999),
        };
        assert_eq!(V1Receipt::decode("ack", ASB_ACK.as_bytes()), Ok(asb));
        assert_eq!(asb.encode(), ASB_ACK, "asb ack writes the view's bare line");
        assert_eq!(asb.kind(), "ack");

        let receipt = V1Receipt::decode("ack", ATERM_RECEIPT.as_bytes()).expect("aterm's receipt");
        assert_eq!(
            receipt,
            V1Receipt::Ack {
                re: Offset(41),
                verdict: Some(ReceiptVerdict::Handled),
                sender_t_ms: Some(1_700_000_000_999),
            }
        );
        assert_eq!(receipt.re(), Offset(41));

        // A session's own `post kind=ack re=41`: it settles ask 41 for aterm's asker, so
        // the view reads it, with no verdict.
        let posted =
            V1Receipt::decode("ack", ATERM_POSTED_ACK.as_bytes()).expect("aterm's posted ack");
        assert_eq!(
            posted,
            V1Receipt::Ack {
                re: Offset(41),
                verdict: None,
                sender_t_ms: Some(1_700_000_000_999),
            }
        );
        assert_eq!(posted.encode(), "v=1 t=1700000000999 re=41");

        let expired =
            V1Receipt::decode("expired", ATERM_EXPIRED.as_bytes()).expect("aterm's verdict");
        assert_eq!(
            expired,
            V1Receipt::Expired {
                re: Offset(7),
                dl_ms: 240_000,
                sender_t_ms: Some(1_700_000_000_999),
            }
        );
        assert_eq!(expired.kind(), "expired");
        assert_eq!(expired.sender_t_ms(), Some(1_700_000_000_999));

        for wire in [ASB_ACK, ATERM_RECEIPT, ATERM_POSTED_ACK, ATERM_EXPIRED] {
            assert_eq!(
                FabricReceipt::decode(wire),
                Err(ReceiptError::UnknownKind),
                "{wire:?}"
            );
        }
    }

    /// [`ReceiptVerdict::ALL`] is the vocabulary: every word in it parses back to itself
    /// and is read by the view, the words are distinct, and nothing else is a verdict.
    /// The match below is exhaustive: a verdict added to the enum fails to compile here,
    /// and belongs in `ALL` at the index it is given.
    #[test]
    fn all_is_every_verdict_and_the_views_vocabulary() {
        const fn index(v: ReceiptVerdict) -> usize {
            match v {
                ReceiptVerdict::Handled => 0,
                ReceiptVerdict::Refused => 1,
                ReceiptVerdict::Deferred => 2,
            }
        }
        for (i, verdict) in ReceiptVerdict::ALL.into_iter().enumerate() {
            assert_eq!(index(verdict), i, "{verdict}");
            assert_eq!(ReceiptVerdict::parse(verdict.as_str()), Ok(verdict));
            let body = format!("v=1 re=3 verdict={verdict}");
            assert_eq!(
                V1Receipt::decode("ack", body.as_bytes()),
                Ok(V1Receipt::Ack {
                    re: Offset(3),
                    verdict: Some(verdict),
                    sender_t_ms: None,
                })
            );
        }
        for word in ["", "handle", "handledd", "HANDLED", "cancelled"] {
            assert_eq!(
                ReceiptVerdict::parse(word),
                Err(ReceiptError::InvalidVerdict),
                "{word:?}"
            );
        }
    }

    /// What the view refuses, each beside the line it refuses being read (the negative
    /// controls are the three writers' lines above, which decode).
    #[test]
    fn the_view_refuses_what_is_not_a_receipt() {
        let refused = |kind: &str, body: &str| V1Receipt::decode(kind, body.as_bytes());
        // The kind is the subject's, and only the two receipt kinds have a view.
        for kind in ["answer", "ask", "", "ACK", "ack "] {
            assert_eq!(
                refused(kind, ASB_ACK),
                Err(ReceiptError::UnknownKind),
                "{kind:?}"
            );
        }
        // The other kind's field does not stand in for this kind's: an `expired` needs its
        // `dl=`, and an `ack`'s `dl=` is skipped unread (on an `ack` lane, an expired-shaped
        // body is a verdict-less `ack`, as aterm's asker reads it).
        for ack_body in [ASB_ACK, ATERM_RECEIPT, ATERM_POSTED_ACK] {
            assert_eq!(
                refused("expired", ack_body),
                Err(ReceiptError::MissingOrDuplicateField("dl")),
                "{ack_body:?}"
            );
        }
        assert_eq!(
            refused("ack", ATERM_EXPIRED),
            Ok(V1Receipt::Ack {
                re: Offset(7),
                verdict: None,
                sender_t_ms: Some(1_700_000_000_999),
            })
        );
        // No `re=`: nothing to settle, with a verdict or without one (a session's
        // `post kind=ack` with no `re=` settles no ask on aterm's side either).
        for body in [ATERM_RECEIPT, ATERM_POSTED_ACK] {
            let no_re = body.replace("re=41 ", "");
            assert_eq!(
                refused("ack", &no_re),
                Err(ReceiptError::MissingOrDuplicateField("re")),
                "{no_re:?}"
            );
        }
        // The version is required, and only `1` is read.
        assert_eq!(
            refused("ack", "t=1 re=7 verdict=handled"),
            Err(ReceiptError::MissingOrDuplicateField("v"))
        );
        for v in ["v=2", "v=", "v=11", "v=01", "v=1x"] {
            let body = ASB_ACK.replacen("v=1", v, 1);
            assert_eq!(
                refused("ack", &body),
                Err(ReceiptError::UnknownVersion),
                "{body:?}"
            );
        }
        // The retired spelling carries no verdict: its `state=` is skipped, and the line is
        // a verdict-less `ack` (what aterm's asker read from it, which is why it was
        // retired). A `verdict=` the view reads must be one of the three.
        assert_eq!(
            refused("ack", "v=1 t=1 re=7 state=refused"),
            Ok(V1Receipt::Ack {
                re: Offset(7),
                verdict: None,
                sender_t_ms: Some(1),
            })
        );
        for word in ["maybe", "handled%20now", "Handled", "", "handledx"] {
            let body = format!("v=1 t=1 re=7 verdict={word}");
            assert_eq!(
                refused("ack", &body),
                Err(ReceiptError::InvalidVerdict),
                "{body:?}"
            );
        }
        // Numbers: digits only, in range.
        for (body, field) in [
            ("v=1 re=+7 verdict=handled", "re"),
            ("v=1 re= verdict=handled", "re"),
            ("v=1 re=7x verdict=handled", "re"),
            ("v=1 re=18446744073709551616 verdict=handled", "re"),
            ("v=1 t=-1 re=7 verdict=handled", "t"),
            ("v=1 re=7 dl=4m", "dl"),
        ] {
            let kind = if body.contains("dl=") {
                "expired"
            } else {
                "ack"
            };
            assert_eq!(
                refused(kind, body),
                Err(ReceiptError::InvalidNumber(field)),
                "{body:?}"
            );
        }
        assert_eq!(
            refused("ack", "v=1 re=18446744073709551615 verdict=handled"),
            Ok(V1Receipt::Ack {
                re: Offset(u64::MAX),
                verdict: Some(ReceiptVerdict::Handled),
                sender_t_ms: None,
            })
        );
        // A field the view reads, given twice, is ambiguous.
        for (kind, body, field) in [
            ("ack", "v=1 v=1 re=7 verdict=handled", "v"),
            ("ack", "v=1 t=1 t=2 re=7 verdict=handled", "t"),
            ("ack", "v=1 re=7 re=8 verdict=handled", "re"),
            ("ack", "v=1 re=7 verdict=handled verdict=handled", "verdict"),
            ("expired", "v=1 re=7 dl=1 dl=1", "dl"),
        ] {
            assert_eq!(
                refused(kind, body),
                Err(ReceiptError::MissingOrDuplicateField(field)),
                "{body:?}"
            );
        }
    }

    /// What the view ignores: `from=`, `text=`, unknown keys, keys without `=`, empty
    /// tokens and the other kind's field, in any order; the line ends at the first `\n`.
    #[test]
    fn the_view_ignores_what_it_does_not_read() {
        let want = V1Receipt::Ack {
            re: Offset(41),
            verdict: Some(ReceiptVerdict::Deferred),
            sender_t_ms: None,
        };
        for body in [
            "v=1 re=41 verdict=deferred",
            "text=x%20re=9 lang=en verdict=deferred from=s-a  re=41 v=1 dl=oops",
            "bare v=1 re=41 verdict=deferred ",
            "v=1 re=41 verdict=deferred\nre=9 verdict=refused",
            "v=1 re=41 verdict=deferred\n",
            "v=1 re=41 verdict=deferred text=",
        ] {
            assert_eq!(
                V1Receipt::decode("ack", body.as_bytes()),
                Ok(want),
                "{body:?}"
            );
        }
        // Past the `\n` is not the line: a field there is not read.
        assert_eq!(
            V1Receipt::decode("ack", b"v=1 verdict=deferred\nre=41"),
            Err(ReceiptError::MissingOrDuplicateField("re"))
        );
        // `verdict=` on an `expired` is skipped unread, malformed or not.
        assert_eq!(
            V1Receipt::decode("expired", b"v=1 re=7 dl=9 verdict=maybe"),
            Ok(V1Receipt::Expired {
                re: Offset(7),
                dl_ms: 9,
                sender_t_ms: None,
            })
        );
    }

    fn any_receipt() -> impl Strategy<Value = V1Receipt> {
        let verdict = proptest::option::of(proptest::sample::select(ReceiptVerdict::ALL.to_vec()));
        prop_oneof![
            (any::<u64>(), verdict, any::<Option<u64>>()).prop_map(|(re, verdict, t)| {
                V1Receipt::Ack {
                    re: Offset(re),
                    verdict,
                    sender_t_ms: t,
                }
            }),
            (any::<u64>(), any::<u64>(), any::<Option<u64>>()).prop_map(|(re, dl, t)| {
                V1Receipt::Expired {
                    re: Offset(re),
                    dl_ms: dl,
                    sender_t_ms: t,
                }
            }),
        ]
    }

    proptest! {
        /// Every receipt the view can hold encodes to a line it reads back under its own
        /// kind, with `from=` and `text=` around it as aterm writes them or not.
        #[test]
        fn a_receipt_round_trips_under_its_kind(r in any_receipt(), from in any::<bool>()) {
            let line = r.encode();
            prop_assert_eq!(V1Receipt::decode(r.kind(), line.as_bytes()), Ok(r));
            let dressed = if from {
                line.replacen("v=1", "v=1 from=s-x", 1) + " text=some%20words"
            } else {
                line + " text=some%20words"
            };
            prop_assert_eq!(V1Receipt::decode(r.kind(), dressed.as_bytes()), Ok(r));
        }

        /// The view is total: any bytes, under either kind, give an answer, never a panic.
        #[test]
        fn the_view_is_total_over_any_bytes(
            body in proptest::collection::vec(any::<u8>(), 0..96),
            ack in any::<bool>(),
        ) {
            let kind = if ack { "ack" } else { "expired" };
            let _ = V1Receipt::decode(kind, &body);
        }
    }

    #[test]
    fn clean_origin_monotone_clock_tick_advances_monotonically() {
        assert_eq!(FabricReceipt::tick_clock(1_000, 950), 1_000);
        assert_eq!(FabricReceipt::tick_clock(1_000, 1_000), 1_000);
        assert_eq!(FabricReceipt::tick_clock(1_000, 1_250), 1_250);
    }

    #[test]
    fn v1_node_ack_and_v1_barrier_ack_roundtrip_and_guard_invariants() {
        for state in NodeAckState::ALL {
            let ack = V1NodeAck {
                re: Offset(42),
                state,
                sender_t_ms: Some(1_700_000_000_500),
            };
            let encoded = ack.encode();
            assert_eq!(V1NodeAck::decode(encoded.as_bytes()), Ok(ack));
            assert_eq!(ack.answers_halt_at(Offset(42)), Some(state));
            assert_eq!(ack.answers_halt_at(Offset(41)), None);
            assert_eq!(ack.answers_halt_at(Offset(43)), None);
        }
        assert!(V1NodeAck::decode(b"v=1 re=7 state=invalid").is_err());
        assert!(V1NodeAck::decode(b"v=1 state=held").is_err());

        for state in BarrierAckState::ALL {
            let back = V1BarrierAck {
                re: Some(Offset(100)),
                state,
                sender_t_ms: Some(9_000),
            };
            assert_eq!(
                V1BarrierAck::decode(format!("{} reason=ok", back.encode()).as_bytes()),
                Ok(back)
            );
            assert!(back.valid_for_barrier(Offset(100), Offset(100)));
            assert!(back.valid_for_barrier(Offset(105), Offset(100)));
            // Pre-published ack/<B> (`record_offset < B`) or mismatched `re=` is rejected (§5.4).
            assert!(!back.valid_for_barrier(Offset(99), Offset(100)));
            assert!(!back.valid_for_barrier(Offset(105), Offset(101)));
        }
        assert!(BarrierAckState::Busy.is_liveness_only());
        assert!(BarrierAckState::Absent.is_liveness_only());
        assert!(!BarrierAckState::Ready.is_liveness_only());
        assert!(!BarrierAckState::Refused.is_liveness_only());
        assert!(!BarrierAckState::Held.is_liveness_only());
    }
}
