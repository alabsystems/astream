//! The demo programs — each written ONCE against [`EffectSeam`], run under record
//! and replay. [`run`] reads the three backend doors (clock, rng, file); its
//! digest folds the effects **non-commutatively** (so a replay bug that transposes
//! the two random words is observable), with the file bytes folded last.
//! [`converse`] goes through every door, including the three that carry a value
//! the program supplies (a reply, an output, a flag), and each has an
//! independent oracle over its tape.

use crate::seam::{EffectRecord, EffectSeam, EffectsLog};

const P: u64 = 0x0000_0100_0000_01b3;

// The Clean island, out of line: only a Trust compiler lexes it, so it mounts under
// `cfg(clean_islands)` (build.rs) and a stock compiler never opens the file.
#[cfg(clean_islands)]
#[path = "demo_island.rs"]
mod demo_island;
#[cfg(not(clean_islands))]
pub use crate::twins::demo_clamp_poll_index;
#[cfg(clean_islands)]
pub use demo_island::demo_clamp_poll_index;

contract_fn! {
    /// Verified check that a stop-poll index `idx` is strictly within `max_reads`,
    /// linked via `clean-kernel-defeq` to `demo_poll_in_range_isl`.
    #[must_use]
    pub const fn demo_poll_in_range(idx: u64, max_reads: u64) -> bool
    clauses [ensures result == (idx < max_reads)]
    {
        idx < max_reads
    }
}

/// Fold the four effects into a digest. Non-commutative in `r0`/`r1`.
const fn digest(c: u64, r0: u64, r1: u64, bytes: &[u8]) -> u64 {
    let mut d = c;
    d = d.wrapping_mul(P).wrapping_add(r0);
    d = d.wrapping_mul(P).wrapping_add(r1);
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        d = d.wrapping_mul(P).wrapping_add(b as u64);
        rest = tail;
    }
    d
}

/// The program: read one clock, two random words, then one file — in that fixed
/// order — and fold them. Works against any [`EffectSeam`], so the *same code*
/// runs under record and replay; a seam's refusal (a diverged replay) stops the
/// program at the effect it could not answer and is returned unchanged.
pub fn run<S: EffectSeam>(seam: &mut S, path: &str) -> Result<u64, S::Error> {
    let c = seam.now_nanos()?;
    let r0 = seam.next_rand()?;
    let r1 = seam.next_rand()?;
    let bytes = seam.read_file(path)?;
    Ok(digest(c, r0, r1, &bytes))
}

/// A GENUINELY INDEPENDENT recomputation of the digest — the order-sensitive head
/// is spelled out as a **closed form**, written WITHOUT the `digest` loop, so a
/// copy-paste fold bug (e.g. an `r0`/`r1` transposition or a wrong multiplier in
/// `digest`) cannot also live here: the two would then disagree. Equal to `digest`
/// on correct inputs. So `run(replay) == oracle(recorded values)` catches both
/// replay-machinery bugs (value flows through the seam on one side, directly on the
/// other) AND a shared fold-algorithm bug — never `f(x) == f(x)`.
#[must_use]
pub const fn oracle(c: u64, r0: u64, r1: u64, bytes: &[u8]) -> u64 {
    let mut d = c
        .wrapping_mul(P)
        .wrapping_add(r0)
        .wrapping_mul(P)
        .wrapping_add(r1);
    let mut rest = bytes;
    while let &[b, ref tail @ ..] = rest {
        d = d.wrapping_mul(P).wrapping_add(b as u64);
        rest = tail;
    }
    d
}

/// Extract the `(clock, rand0, rand1, file-bytes)` a tape recorded, in order.
/// Returns `None` unless the tape is exactly `[Clock, Rand, Rand, File]`.
pub fn tape_values(log: &EffectsLog) -> Option<(u64, u64, u64, Vec<u8>)> {
    match log.0.as_slice() {
        [EffectRecord::Clock(c), EffectRecord::Rand(r0), EffectRecord::Rand(r1), EffectRecord::File { bytes, .. }] => {
            Some((*c, *r0, *r1, bytes.clone()))
        }
        _ => None,
    }
}

/// The door the [`converse`] demo sends its question through.
pub const PEER: &str = "peer";
/// The door the [`converse`] demo prints through.
pub const OUT: &str = "out";
/// The flag the [`converse`] demo polls.
pub const STOP: &str = "stop";
/// How many times [`converse`] polls [`STOP`], back to back.
pub const STOP_READS: usize = 4;

/// FNV-1a's offset basis: the [`converse`] digest's starting word, so an
/// all-zero run does not digest to zero.
const OFFSET: u64 = 0xcbf2_9ce4_8422_2325;

/// Pack the [`STOP_READS`] boolean polls into a single `u64` word (`bit i = stops[i]`).
#[must_use]
pub const fn pack_stop_bits(stops: &[bool; STOP_READS]) -> u64 {
    (stops[0] as u64)
        | ((stops[1] as u64) << 1)
        | ((stops[2] as u64) << 2)
        | ((stops[3] as u64) << 3)
}

/// Unpack a `u64` stop-bit word back into its [`STOP_READS`] boolean polls.
#[must_use]
pub const fn unpack_stop_bits(bits: u64) -> [bool; STOP_READS] {
    [
        (bits & 1) != 0,
        ((bits >> 1) & 1) != 0,
        ((bits >> 2) & 1) != 0,
        ((bits >> 3) & 1) != 0,
    ]
}

/// Encode the four scalar `u64` words of a [`ConverseValues`] tape
/// `(mono0, clock, rand, mono1)` into a 32-byte little-endian array.
#[must_use]
pub const fn encode_converse_scalars(mono0: u64, clock: u64, rand: u64, mono1: u64) -> [u8; 32] {
    [
        mono0 as u8,
        (mono0 >> 8) as u8,
        (mono0 >> 16) as u8,
        (mono0 >> 24) as u8,
        (mono0 >> 32) as u8,
        (mono0 >> 40) as u8,
        (mono0 >> 48) as u8,
        (mono0 >> 56) as u8,
        clock as u8,
        (clock >> 8) as u8,
        (clock >> 16) as u8,
        (clock >> 24) as u8,
        (clock >> 32) as u8,
        (clock >> 40) as u8,
        (clock >> 48) as u8,
        (clock >> 56) as u8,
        rand as u8,
        (rand >> 8) as u8,
        (rand >> 16) as u8,
        (rand >> 24) as u8,
        (rand >> 32) as u8,
        (rand >> 40) as u8,
        (rand >> 48) as u8,
        (rand >> 56) as u8,
        mono1 as u8,
        (mono1 >> 8) as u8,
        (mono1 >> 16) as u8,
        (mono1 >> 24) as u8,
        (mono1 >> 32) as u8,
        (mono1 >> 40) as u8,
        (mono1 >> 48) as u8,
        (mono1 >> 56) as u8,
    ]
}

const fn decode_converse_mono0(raw: &[u8; 32]) -> u64 {
    (raw[0] as u64)
        | ((raw[1] as u64) << 8)
        | ((raw[2] as u64) << 16)
        | ((raw[3] as u64) << 24)
        | ((raw[4] as u64) << 32)
        | ((raw[5] as u64) << 40)
        | ((raw[6] as u64) << 48)
        | ((raw[7] as u64) << 56)
}

const fn decode_converse_clock(raw: &[u8; 32]) -> u64 {
    (raw[8] as u64)
        | ((raw[9] as u64) << 8)
        | ((raw[10] as u64) << 16)
        | ((raw[11] as u64) << 24)
        | ((raw[12] as u64) << 32)
        | ((raw[13] as u64) << 40)
        | ((raw[14] as u64) << 48)
        | ((raw[15] as u64) << 56)
}

const fn decode_converse_rand(raw: &[u8; 32]) -> u64 {
    (raw[16] as u64)
        | ((raw[17] as u64) << 8)
        | ((raw[18] as u64) << 16)
        | ((raw[19] as u64) << 24)
        | ((raw[20] as u64) << 32)
        | ((raw[21] as u64) << 40)
        | ((raw[22] as u64) << 48)
        | ((raw[23] as u64) << 56)
}

const fn decode_converse_mono1(raw: &[u8; 32]) -> u64 {
    (raw[24] as u64)
        | ((raw[25] as u64) << 8)
        | ((raw[26] as u64) << 16)
        | ((raw[27] as u64) << 24)
        | ((raw[28] as u64) << 32)
        | ((raw[29] as u64) << 40)
        | ((raw[30] as u64) << 48)
        | ((raw[31] as u64) << 56)
}

/// Decode the four scalar `u64` words `(mono0, clock, rand, mono1)` from a 32-byte
/// little-endian array.
#[must_use]
pub const fn decode_converse_scalars(raw: &[u8; 32]) -> (u64, u64, u64, u64) {
    (
        decode_converse_mono0(raw),
        decode_converse_clock(raw),
        decode_converse_rand(raw),
        decode_converse_mono1(raw),
    )
}

const ASK_HEX: [u8; 16] = *b"0123456789abcdef";

const fn ask_hex_hi(rand: u64) -> [u8; 8] {
    [
        ASK_HEX[((rand >> 60) & 0xF) as usize],
        ASK_HEX[((rand >> 56) & 0xF) as usize],
        ASK_HEX[((rand >> 52) & 0xF) as usize],
        ASK_HEX[((rand >> 48) & 0xF) as usize],
        ASK_HEX[((rand >> 44) & 0xF) as usize],
        ASK_HEX[((rand >> 40) & 0xF) as usize],
        ASK_HEX[((rand >> 36) & 0xF) as usize],
        ASK_HEX[((rand >> 32) & 0xF) as usize],
    ]
}

const fn ask_hex_lo(rand: u64) -> [u8; 8] {
    [
        ASK_HEX[((rand >> 28) & 0xF) as usize],
        ASK_HEX[((rand >> 24) & 0xF) as usize],
        ASK_HEX[((rand >> 20) & 0xF) as usize],
        ASK_HEX[((rand >> 16) & 0xF) as usize],
        ASK_HEX[((rand >> 12) & 0xF) as usize],
        ASK_HEX[((rand >> 8) & 0xF) as usize],
        ASK_HEX[((rand >> 4) & 0xF) as usize],
        ASK_HEX[(rand & 0xF) as usize],
    ]
}

const fn ask_hex_bytes(rand: u64) -> [u8; 16] {
    let [h0, h1, h2, h3, h4, h5, h6, h7] = ask_hex_hi(rand);
    let [l0, l1, l2, l3, l4, l5, l6, l7] = ask_hex_lo(rand);
    [
        h0, h1, h2, h3, h4, h5, h6, h7, l0, l1, l2, l3, l4, l5, l6, l7,
    ]
}

const fn encode_dec_len(mut n: usize) -> ([u8; 32], usize) {
    let mut dec = [0u8; 32];
    let mut idx = 19usize;
    dec[19] = b'0' | ((n % 10) as u8);
    n /= 10;
    while n > 0 && idx > 0 {
        idx -= 1;
        dec[idx & 31] = b'0' | ((n % 10) as u8);
        n /= 10;
    }
    (dec, idx)
}

/// The question [`converse`] asks: built from the random word and the file it
/// read, so a replay fed a wrong value asks a DIFFERENT question — which the
/// reply door refuses as a diverged request — instead of silently receiving
/// the recorded answer to a question it did not ask.
pub fn ask(rand: u64, file: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(50);
    out.extend_from_slice(b"ask rand=");
    let hex_bytes = ask_hex_bytes(rand);
    out.extend_from_slice(&hex_bytes);
    out.extend_from_slice(b" len=");
    let (dec, mut idx) = encode_dec_len(file.len());
    while idx < 20 {
        out.push(dec[idx & 31]);
        idx += 1;
    }
    out
}

/// What [`converse`] prints for a reply.
pub fn say(reply: &[u8]) -> Vec<u8> {
    let mut line = Vec::new();
    line.extend_from_slice(b"got ");
    line.extend_from_slice(reply);
    line
}

/// The program's running digest: one multiply-add per word, a length word
/// before every byte string so adjacent strings cannot slide into each other.
struct Digest(u64);

impl Digest {
    const fn word(&mut self, w: u64) {
        self.0 = self.0.wrapping_mul(P).wrapping_add(w);
    }
    const fn bytes(&mut self, b: &[u8]) {
        self.word(b.len() as u64);
        let mut rest = b;
        while let &[x, ref tail @ ..] = rest {
            self.word(x as u64);
            rest = tail;
        }
    }
}

/// The doors demo: a program that goes through EVERY door of [`EffectSeam`],
/// in a fixed order, and folds everything it saw and said into one digest:
///
/// 1. a monotonic read, a wall-clock read, a random word, one file;
/// 2. one [`exchange`](EffectSeam::exchange) through [`PEER`] whose request
///    ([`ask`]) depends on the random word and the file;
/// 3. one [`emit`](EffectSeam::emit) through [`OUT`] of [`say`]`(reply)`;
/// 4. [`STOP_READS`] back-to-back [`raised`](EffectSeam::raised) reads of
///    [`STOP`], with nothing between them on the tape;
/// 5. a closing monotonic read.
///
/// `peer` and `stop` are the live world of the two closure doors. The same
/// code runs under every seam; a replay must never call either.
pub fn converse<S: EffectSeam>(
    seam: &mut S,
    path: &str,
    peer: &mut dyn FnMut(&[u8]) -> Vec<u8>,
    stop: &mut dyn FnMut() -> bool,
) -> Result<u64, S::Error> {
    let mono0 = seam.mono_nanos()?;
    let clock = seam.now_nanos()?;
    let rand = seam.next_rand()?;
    let file = seam.read_file(path)?;
    let ask_op: fn(u64, &[u8]) -> Vec<u8> = ask;
    let request = ask_op(rand, &file);
    let exchange_op: fn(_, _, _, _) -> _ = EffectSeam::exchange;
    let reply = exchange_op(seam, PEER, &request, peer)?;
    let say_op: fn(&[u8]) -> Vec<u8> = say;
    let said = say_op(&reply);
    seam.emit(OUT, &said)?;
    let mut stops = [false; STOP_READS];
    for read in &mut stops {
        let raised_op: fn(_, _, _) -> _ = EffectSeam::raised;
        *read = raised_op(seam, STOP, stop)?;
    }
    let mono1 = seam.mono_nanos()?;

    let mut d = Digest(OFFSET);
    d.word(mono0);
    d.word(clock);
    d.word(rand);
    d.bytes(&file);
    d.bytes(&request);
    d.bytes(&reply);
    d.bytes(&said);
    // The flag reads as one word, bit i = read i.
    d.word(pack_stop_bits(&stops));
    d.word(mono1);
    Ok(d.0)
}

/// Everything a [`converse`] tape recorded, read straight off its records.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConverseValues {
    /// The opening monotonic read.
    pub mono0: u64,
    /// The wall-clock read.
    pub clock: u64,
    /// The random word.
    pub rand: u64,
    /// The file's bytes.
    pub file: Vec<u8>,
    /// The request the program sent through [`PEER`], as taped.
    pub request: Vec<u8>,
    /// The reply the peer returned, as taped.
    pub reply: Vec<u8>,
    /// What the program printed through [`OUT`], as taped.
    pub said: Vec<u8>,
    /// The read of [`STOP`] that first answered true, if one did (`0` is the
    /// first read) — the taped `Raised` record's false-read count.
    pub raised_at: Option<u64>,
    /// The closing monotonic read.
    pub mono1: u64,
}

/// Read a [`converse`] tape's values. `None` unless the tape is exactly
/// `[Mono, Clock, Rand, File, Exchange(peer), Emit(out), (Raised(stop))?, Mono]`
/// with a `Raised` count inside the polls the program makes.
pub fn converse_values(log: &EffectsLog) -> Option<ConverseValues> {
    use EffectRecord as R;
    let (mono0, clock, rand, file, peer, request, reply, out, said, raised_at, mono1) = match log
        .0
        .as_slice()
    {
        [R::Mono(mono0), R::Clock(clock), R::Rand(rand), R::File { bytes: file, .. }, R::Exchange {
            door: peer,
            request,
            reply,
        }, R::Emit {
            door: out,
            bytes: said,
        }, R::Raised { door, false_reads }, R::Mono(mono1)]
            if door == STOP && demo_poll_in_range(*false_reads, STOP_READS as u64) =>
        {
            (
                mono0,
                clock,
                rand,
                file,
                peer,
                request,
                reply,
                out,
                said,
                Some(*false_reads),
                mono1,
            )
        }
        [R::Mono(mono0), R::Clock(clock), R::Rand(rand), R::File { bytes: file, .. }, R::Exchange {
            door: peer,
            request,
            reply,
        }, R::Emit {
            door: out,
            bytes: said,
        }, R::Mono(mono1)] => (
            mono0, clock, rand, file, peer, request, reply, out, said, None, mono1,
        ),
        _ => return None,
    };
    if peer == PEER && out == OUT {
        Some(ConverseValues {
            mono0: *mono0,
            clock: *clock,
            rand: *rand,
            file: file.clone(),
            request: request.clone(),
            reply: reply.clone(),
            said: said.clone(),
            raised_at,
            mono1: *mono1,
        })
    } else {
        None
    }
}

/// A GENUINELY INDEPENDENT recomputation of [`converse`]'s digest from the
/// values its tape holds. It does not call [`ask`] or [`say`] and does not run
/// the program's fold: it lays every word out in one flat list and folds that,
/// and it derives the four flag answers from the `Raised` count, not from
/// replaying the flag door. So `converse(replay) == converse_oracle(tape)`
/// says the replayed program asked exactly the taped request, printed exactly
/// the taped output and saw the flag rise at exactly the taped read — through
/// two different pieces of code.
pub fn converse_oracle(v: &ConverseValues) -> u64 {
    // Bits raised_at..STOP_READS: every read from the first true one on.
    let all = (1u64 << STOP_READS) - 1;
    let stop_bits = v.raised_at.map_or(0, |n| {
        #[expect(
            clippy::manual_unwrap_or,
            reason = "a812042 spelled `unwrap_or` as a match for the verified lane; keep its form"
        )]
        let shift = match u32::try_from(n) {
            Ok(k) => k,
            Err(_) => u32::MAX,
        };
        all.checked_shl(shift).unwrap_or(0) & all
    });
    let mut words = vec![v.mono0, v.clock, v.rand];
    for s in [&v.file, &v.request, &v.reply, &v.said] {
        words.push(s.len() as u64);
        for &b in s {
            words.push(b as u64);
        }
    }
    words.push(stop_bits);
    words.push(v.mono1);
    words
        .iter()
        .fold(OFFSET, |d, &w| d.wrapping_mul(P).wrapping_add(w))
}
