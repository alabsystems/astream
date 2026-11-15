// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! A log's identity and lineage as the bus carries them: [`LogIdentity`] (WHICH log, and
//! WHICH incarnation of its offsets) with its `<id>.<generation>` text form and its
//! 24-byte wire form, and [`Lineage`] (where two generations of one log still agree) with
//! [`LogIdentity::continues`], the one reading of it.
//!
//! The vocabulary lives here, beside the frame and the subject grammar, so that a reader
//! that keeps offsets OUTSIDE the log — an embedder's bridge, a session endpoint, a cursor
//! file — parses, compares and continues an identity exactly as astream does without
//! linking the broker. What a consumer does when the identity changes, and when a broker
//! moves it (the `<log>.id` sidecar, the unclean-stop rules, a replica adopting its
//! leader's), is `astream-broker`'s `logid` module's to say; a broker re-exports both
//! types from there.

use std::fmt;

/// WHICH log, and WHICH incarnation of its offsets. Any difference, in
/// [`id`](Self::id) or in [`generation`](Self::generation), means every offset kept
/// under the old identity is meaningless against this log, unless
/// [`continues`](Self::continues) says how far the two still agree (`astream-broker`'s
/// `logid` module says what a consumer does).
///
/// Displayed (and [parsed](Self::parse)) as `<id in 32 lowercase hex>.<generation>`,
/// the form to persist beside the offsets it vouches for. Compare identities as values,
/// never as text: [`parse`](Self::parse) takes a zero-padded generation (`<id>.01` is
/// `<id>.1`), and [`Display`](fmt::Display) writes the one canonical form.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct LogIdentity {
    /// Names the log: random when the log was created (or the identity it had cannot
    /// be read back), derived from its bytes when it predates log identity, and on a
    /// replica its leader's. Two different logs differ here.
    pub id: [u8; 16],
    /// Counts the rewrites of THIS log that may have given one of its offsets to a
    /// different record (a repair's truncation, a log found shorter than, or different
    /// from, what its last open saw). Same `id`, different generation: the same log
    /// file, but its old offsets are as meaningless as another log's.
    pub generation: u64,
}

const INVALID_HEX_SENTINEL: u16 = 0x0100;

const fn decode_lower_nibble_u16(b: u8) -> u16 {
    if b >= b'0' && b <= b'9' {
        (b - b'0') as u16
    } else if b >= b'a' && b <= b'f' {
        (b - b'a' + 10) as u16
    } else {
        INVALID_HEX_SENTINEL
    }
}

const fn decode_lower_hex_u16(hi: u8, lo: u8) -> u16 {
    let h = decode_lower_nibble_u16(hi);
    let l = decode_lower_nibble_u16(lo);
    ((h & 0x0f) << 4) | (l & 0x0f) | ((h | l) & INVALID_HEX_SENTINEL)
}

const fn decode_id_hex(bytes: &[u8; 32]) -> Option<[u8; 16]> {
    let mut rest: &[u8] = bytes;
    let mut hi_half = 0u64;
    let mut lo_half = 0u64;
    let mut pairs = 0usize;
    while let &[hi, lo, ref tail @ ..] = rest {
        let b = decode_lower_hex_u16(hi, lo);
        if (b & INVALID_HEX_SENTINEL) != 0 {
            return None;
        }
        let byte_u64 = (b & 0xff) as u64;
        if pairs < 8 {
            hi_half = hi_half.wrapping_shl(8) | byte_u64;
        } else {
            lo_half = lo_half.wrapping_shl(8) | byte_u64;
        }
        pairs = pairs.saturating_add(1);
        rest = tail;
    }
    if pairs != 16 || !rest.is_empty() {
        return None;
    }
    let [r0, r1, r2, r3, r4, r5, r6, r7] = hi_half.to_be_bytes();
    let [r8, r9, r10, r11, r12, r13, r14, r15] = lo_half.to_be_bytes();
    Some([
        r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
    ])
}

const fn decode_decimal_digit(b: u8) -> Option<u64> {
    if b >= b'0' && b <= b'9' {
        Some((b - b'0') as u64)
    } else {
        None
    }
}

const fn parse_u64_ascii_bytes(bytes: &[u8]) -> Option<u64> {
    let mut rest = bytes;
    if rest.is_empty() {
        return None;
    }
    let mut acc = 0u64;
    while let &[b, ref tail @ ..] = rest {
        let Some(d) = decode_decimal_digit(b) else {
            return None;
        };
        let Some(mul) = acc.checked_mul(10) else {
            return None;
        };
        let Some(next) = mul.checked_add(d) else {
            return None;
        };
        acc = next;
        rest = tail;
    }
    Some(acc)
}

const fn decode_u64_le_bytes(b: &[u8; 8]) -> u64 {
    (b[0] as u64)
        | ((b[1] as u64) << 8)
        | ((b[2] as u64) << 16)
        | ((b[3] as u64) << 24)
        | ((b[4] as u64) << 32)
        | ((b[5] as u64) << 40)
        | ((b[6] as u64) << 48)
        | ((b[7] as u64) << 56)
}

const fn encode_lineage_step(g: u64, c: u64) -> [u8; 16] {
    [
        g as u8,
        (g >> 8) as u8,
        (g >> 16) as u8,
        (g >> 24) as u8,
        (g >> 32) as u8,
        (g >> 40) as u8,
        (g >> 48) as u8,
        (g >> 56) as u8,
        c as u8,
        (c >> 8) as u8,
        (c >> 16) as u8,
        (c >> 24) as u8,
        (c >> 32) as u8,
        (c >> 40) as u8,
        (c >> 48) as u8,
        (c >> 56) as u8,
    ]
}

const fn decode_lineage_step(s: &[u8; 16]) -> (u64, u64) {
    let &[s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15] = s;
    let g = decode_u64_le_bytes(&[s0, s1, s2, s3, s4, s5, s6, s7]);
    let c = decode_u64_le_bytes(&[s8, s9, s10, s11, s12, s13, s14, s15]);
    (g, c)
}

impl LogIdentity {
    /// Bytes the identity takes on the wire: the `id`, then the generation as a
    /// little-endian `u64`.
    pub const WIRE_LEN: usize = 24;

    const fn to_wire(self) -> [u8; Self::WIRE_LEN] {
        let g = self.generation;
        [
            self.id[0],
            self.id[1],
            self.id[2],
            self.id[3],
            self.id[4],
            self.id[5],
            self.id[6],
            self.id[7],
            self.id[8],
            self.id[9],
            self.id[10],
            self.id[11],
            self.id[12],
            self.id[13],
            self.id[14],
            self.id[15],
            g as u8,
            (g >> 8) as u8,
            (g >> 16) as u8,
            (g >> 24) as u8,
            (g >> 32) as u8,
            (g >> 40) as u8,
            (g >> 48) as u8,
            (g >> 56) as u8,
        ]
    }

    const fn decode_wire(b: &[u8; Self::WIRE_LEN]) -> LogIdentity {
        let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23] =
            b;
        let id = [
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15,
        ];
        let generation = decode_u64_le_bytes(&[b16, b17, b18, b19, b20, b21, b22, b23]);
        LogIdentity { id, generation }
    }

    /// Append the wire form to `out`. The broker's protocol and sidecar encoders call
    /// it; the layout is theirs, not a public format.
    #[doc(hidden)]
    pub fn put(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.to_wire());
    }

    /// Read the wire form from the first [`WIRE_LEN`](Self::WIRE_LEN) bytes of `b`. The
    /// broker's protocol decoder calls it; the layout is its own, not a public format.
    #[doc(hidden)]
    pub const fn from_wire(b: &[u8]) -> Option<LogIdentity> {
        let &[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, ref _rest @ ..] =
            b
        else {
            return None;
        };
        Some(Self::decode_wire(&[
            b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18,
            b19, b20, b21, b22, b23,
        ]))
    }

    /// Parse the [`Display`](fmt::Display) form, `<32 lowercase hex>.<generation>`.
    /// Exactly that form: anything else (upper case, a sign, a missing part) is `None`.
    /// The generation is decimal digits whose value fits a `u64`, leading zeros
    /// included, so `<id>.01` and `<id>.1` are one identity.
    pub const fn parse(s: &str) -> Option<LogIdentity> {
        let &[h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, b'.', ref gen_bytes @ ..] =
            s.as_bytes()
        else {
            return None;
        };
        let Some(id) = decode_id_hex(&[
            h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
            h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31,
        ]) else {
            return None;
        };
        let Some(generation) = parse_u64_ascii_bytes(gen_bytes) else {
            return None;
        };
        Some(LogIdentity { id, generation })
    }
}

impl fmt::Display for LogIdentity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for b in &self.id {
            write!(f, "{b:02x}")?;
        }
        write!(f, ".{}", self.generation)
    }
}

/// Where two generations of one log agree: `(generation, common)` steps, newest last,
/// at most [`Lineage::MAX`] of them. A step `(g, c)` says offsets below `c` name the same
/// records under generation `g - 1` and generation `g` — recorded by a broker when the
/// generation moved for a loss the log can bound (an unclean stop, a torn batch cut, a
/// repair's cut), never for a log found shorter, re-based or foreign. See
/// [`LogIdentity::continues`], which reads it; `astream-broker`'s `logid` module says when
/// a step is recorded.
///
/// Told to clients in the answer to `Hello` (`Client::log_lineage`), beside the
/// identity it qualifies.
#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct Lineage {
    steps: Vec<(u64, u64)>,
}

impl Lineage {
    /// The most steps kept: older ones fall off, and a reader whose generation is older
    /// than the window forgets, as before lineage existed.
    pub const MAX: usize = 8;

    /// The steps, `(generation, common)`, oldest first.
    #[must_use]
    pub fn steps(&self) -> &[(u64, u64)] {
        &self.steps
    }

    /// The lineage of these `(generation, common)` steps, oldest first: exactly the one a
    /// `Hello` answer carrying them decodes to (`Client::log_lineage`), and `None` for
    /// steps that decoder refuses — more than [`MAX`](Self::MAX), or generations that do
    /// not rise. The two rules are the wire's own (`validate_lineage_wire`); nothing else
    /// is checked, because the decoder checks nothing else: a `common` is any offset.
    ///
    /// WHY IT IS PUBLIC. A reader that keeps offsets outside the log — an embedder's
    /// bridge, a cursor file — has to be tested against lineages no single real unclean
    /// open makes: a chain longer than one reboot's, a step missing, a window outrun,
    /// commons that fall. Without this the one door outside the crate was the `Hello`
    /// answer, so such a test hand-encoded the extension block (tag `0x02`, its length,
    /// the steps) and parsed it back through `proto::decode_response`, which pins a
    /// private layout in someone else's test. This grants nothing new: any broker, or any
    /// bytes a client parses, can already tell a client every lineage the decoder accepts.
    /// What a lineage MEANS stays the broker's to say — only an open records one in
    /// `<log>.id`, and nothing here writes it.
    #[must_use]
    pub fn from_steps(steps: &[(u64, u64)]) -> Option<Lineage> {
        if steps.len() > Self::MAX {
            return None;
        }
        let mut prev: Option<u64> = None;
        for &(g, _) in steps {
            if let Some(p) = prev {
                if g <= p {
                    return None;
                }
            }
            prev = Some(g);
        }
        Some(Lineage {
            steps: steps.to_vec(),
        })
    }

    /// Append the wire form: `n u8`, then `n × (generation u64 LE, common u64 LE)`. The
    /// broker's protocol and sidecar encoders call it; the layout is theirs, not a public
    /// format.
    #[doc(hidden)]
    pub fn put(&self, out: &mut Vec<u8>) {
        out.push(self.steps.len() as u8);
        for &(g, c) in &self.steps {
            out.extend_from_slice(&encode_lineage_step(g, c));
        }
    }

    /// Read the wire form, which must fill `b` exactly; `None` for a short or long
    /// body, more than [`MAX`](Self::MAX) steps, or generations that do not rise. The
    /// broker's protocol and sidecar decoders call it.
    #[doc(hidden)]
    #[must_use]
    pub fn from_wire(b: &[u8]) -> Option<Lineage> {
        let rest = validate_lineage_wire(b)?;
        let (chunks, _) = rest.as_chunks::<16>();
        let mut steps = Vec::new();
        for chunk in chunks {
            steps.push(decode_lineage_step(chunk));
        }
        Some(Lineage { steps })
    }
}

const fn lineage_generations_strictly_increasing(mut rest: &[u8]) -> bool {
    let mut prev_gen: Option<u64> = None;
    while let &[b0, b1, b2, b3, b4, b5, b6, b7, _, _, _, _, _, _, _, _, ref tail @ ..] = rest {
        let g = decode_u64_le_bytes(&[b0, b1, b2, b3, b4, b5, b6, b7]);
        if let Some(pg) = prev_gen {
            if g <= pg {
                return false;
            }
        }
        prev_gen = Some(g);
        rest = tail;
    }
    rest.is_empty()
}

const fn validate_lineage_wire(b: &[u8]) -> Option<&[u8]> {
    let &[n, ref rest @ ..] = b else {
        return None;
    };
    let n = n as usize;
    if n > Lineage::MAX || rest.len() != n * 16 {
        return None;
    }
    if !lineage_generations_strictly_increasing(rest) {
        return None;
    }
    Some(rest)
}

impl LogIdentity {
    /// Whether offsets a reader kept under `earlier` still name records here, and how
    /// far: `Some(k)` means every offset below `k` names the same record under both, so
    /// the reader resumes at `min(cursor, k)` — skipping nothing, re-reading nothing
    /// below the fork. `Some(u64::MAX)` is the same identity (nothing moved). `None` is
    /// another log as far as this can tell — another `id`, a generation newer than this
    /// one, or a chain with a step missing (a move recorded without lineage, or one older
    /// than the window) — and the reader forgets its offsets, exactly as before lineage.
    ///
    /// `lineage` is the one told beside `self` (the answer to the same `Hello`).
    #[must_use]
    pub fn continues(&self, earlier: LogIdentity, lineage: &Lineage) -> Option<u64> {
        if earlier.id != self.id || earlier.generation > self.generation {
            return None;
        }
        // The same identity, nothing moved: answered before the walk, whose first
        // generation (`earlier + 1`) does not exist at `u64::MAX`.
        if earlier.generation == self.generation {
            return Some(u64::MAX);
        }
        let mut agree = u64::MAX;
        for generation in earlier.generation.checked_add(1)?..=self.generation {
            let mut found = None;
            for &(g, c) in &lineage.steps {
                if g == generation {
                    found = Some(c);
                    break;
                }
            }
            let common = found?;
            agree = agree.min(common);
        }
        Some(agree)
    }

    /// Whether `earlier` is an earlier generation of this same log: the same `id`, a
    /// lower `generation`. These are exactly the pairs other than `earlier == self` that
    /// [`continues`](Self::continues) can answer `Some` for — the ones some lineage can
    /// carry across — so a reader told "`self` continues `earlier` up to `k`" without the
    /// lineage itself (a bridge relaying what it read in a `Hello`) checks the claim is
    /// one a lineage could make, and refuses any other.
    #[must_use]
    pub fn continues_from(&self, earlier: LogIdentity) -> bool {
        earlier.id == self.id && earlier.generation < self.generation
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ident(byte: u8, generation: u64) -> LogIdentity {
        LogIdentity {
            id: [byte; 16],
            generation,
        }
    }

    #[test]
    fn the_display_form_round_trips_and_nothing_else_parses() {
        let i = LogIdentity {
            id: *b"\x00\x01\x02\x03\x04\x05\x06\x07\x08\x09\x0a\x0b\x0c\xfd\xfe\xff",
            generation: 42,
        };
        let s = i.to_string();
        assert_eq!(s, "000102030405060708090a0b0cfdfeff.42");
        assert_eq!(LogIdentity::parse(&s), Some(i));
        for bad in [
            "",
            "000102030405060708090a0b0cfdfeff",
            "000102030405060708090a0b0cfdfeff.",
            "000102030405060708090A0B0CFDFEFF.42",
            "000102030405060708090a0b0cfdfeff.+42",
            "000102030405060708090a0b0cfdfe.42",
            "+00102030405060708090a0b0cfdfeff.42",
            "000102030405060708090a0b0cfdfeff.18446744073709551616",
            "000102030405060708090a0b0cfdfeff.4 2",
            "000102030405060708090a0b0cfdfeff.42 ",
            "000102030405060708090a0b0cfdfeff.-1",
        ] {
            assert_eq!(LogIdentity::parse(bad), None, "{bad:?}");
        }
    }

    /// A zero-padded generation is the same identity as the canonical one, at any length
    /// whose value fits — past the 20 digits of `u64::MAX` included — and `Display` writes
    /// it back in the canonical form, the one to persist.
    #[test]
    fn a_zero_padded_generation_is_the_canonical_identity() {
        let hex = "000102030405060708090a0b0cfdfeff";
        let canonical = LogIdentity::parse(&format!("{hex}.1")).expect("canonical");
        for padded in [
            format!("{hex}.01"),
            format!("{hex}.0000000000000000000000001"),
        ] {
            let parsed = LogIdentity::parse(&padded).expect("a padded generation parses");
            assert_eq!(parsed, canonical, "{padded}");
            assert_eq!(parsed.to_string(), format!("{hex}.1"), "{padded}");
        }
        let max = format!("{hex}.000{}", u64::MAX);
        assert_eq!(
            LogIdentity::parse(&max).map(|i| i.generation),
            Some(u64::MAX)
        );
        assert_eq!(
            LogIdentity::parse(&format!("{hex}.000{}0", u64::MAX)),
            None,
            "a value past u64::MAX, however padded"
        );
        assert_eq!(
            LogIdentity::parse(&format!("{hex}.0")).map(|i| i.generation),
            Some(0)
        );
    }

    #[test]
    fn the_wire_form_round_trips() {
        let i = ident(7, u64::MAX);
        let mut b = Vec::new();
        i.put(&mut b);
        assert_eq!(b.len(), LogIdentity::WIRE_LEN);
        assert_eq!(LogIdentity::from_wire(&b), Some(i));
        assert_eq!(LogIdentity::from_wire(&b[..23]), None);
    }

    /// `continues` reads the chain: the same identity continues everywhere, an earlier
    /// generation resumes at the lowest common since, and a gap in the chain, a window
    /// outrun, another id or a newer generation does not continue. The lineage's wire
    /// form round trips, and a falling one does not decode.
    #[test]
    fn continues_reads_the_chain_and_the_lineage_wire_form_round_trips() {
        let l = Lineage::from_steps(&[(1, 7), (2, 7), (3, 9)]).expect("rising");
        let now = ident(5, 3);
        assert_eq!(now.continues(ident(5, 3), &l), Some(u64::MAX));
        assert_eq!(
            ident(5, u64::MAX).continues(ident(5, u64::MAX), &Lineage::default()),
            Some(u64::MAX),
            "the same identity at the last generation"
        );
        assert_eq!(now.continues(ident(5, 2), &l), Some(9));
        assert_eq!(now.continues(ident(5, 0), &l), Some(7));
        assert_eq!(now.continues(ident(6, 0), &l), None, "another log");
        assert_eq!(
            ident(5, 2).continues(ident(5, 3), &l),
            None,
            "a newer generation"
        );
        let gap = Lineage::from_steps(&[(1, 10), (3, 9)]).expect("rising");
        assert_eq!(
            now.continues(ident(5, 0), &gap),
            None,
            "a move without lineage"
        );
        let window: Vec<(u64, u64)> = (3..=10).map(|g| (g, 90)).collect();
        let window = Lineage::from_steps(&window).expect("eight rising steps");
        assert_eq!(
            ident(5, 10).continues(ident(5, 1), &window),
            None,
            "older than the window"
        );
        assert_eq!(ident(5, 10).continues(ident(5, 2), &window), Some(90));
        let mut wire = Vec::new();
        l.put(&mut wire);
        assert_eq!(Lineage::from_wire(&wire), Some(l.clone()));
        assert_eq!(Lineage::from_wire(&wire[..wire.len() - 1]), None);
        let mut falling = Vec::new();
        Lineage {
            steps: vec![(3, 1), (2, 1)],
        }
        .put(&mut falling);
        assert_eq!(Lineage::from_wire(&falling), None, "generations must rise");
    }

    /// `continues_from` holds for exactly the pairs other than `earlier == self` that
    /// `continues` answers `Some` for under a lineage holding every step the pair could
    /// need, over every pair of identities on two ids and the generations `0..=8` (a full
    /// lineage of [`Lineage::MAX`] steps covers each), and the pairs at `u64::MAX`.
    ///
    /// Negative controls, on the same sweep: a `continues_from` that ignores the id and
    /// one that admits the same generation each disagree with `continues`, so the sweep
    /// reaches both of its rules.
    #[test]
    fn continues_from_is_what_a_full_lineage_lets_continues_carry() {
        fn disagreements(
            pairs: &[(LogIdentity, LogIdentity, &Lineage)],
            claim: impl Fn(LogIdentity, LogIdentity) -> bool,
        ) -> usize {
            pairs
                .iter()
                .filter(|(now, earlier, full)| {
                    let carried = now != earlier && now.continues(*earlier, full).is_some();
                    claim(*now, *earlier) != carried
                })
                .count()
        }
        let low: Vec<(u64, u64)> = (1..=8).map(|g| (g, 100 - g)).collect();
        let low = Lineage::from_steps(&low).expect("eight rising steps");
        let high = Lineage::from_steps(&[(u64::MAX - 1, 4), (u64::MAX, 3)]).expect("rising");
        let mut pairs = Vec::new();
        for (gens, full) in [
            ((0..=8).collect::<Vec<u64>>(), &low),
            (vec![u64::MAX - 2, u64::MAX - 1, u64::MAX], &high),
        ] {
            for &a in &[ident(1, 0), ident(2, 0)] {
                for &b in &[ident(1, 0), ident(2, 0)] {
                    for &ga in &gens {
                        for &gb in &gens {
                            let now = LogIdentity {
                                generation: ga,
                                ..a
                            };
                            let earlier = LogIdentity {
                                generation: gb,
                                ..b
                            };
                            pairs.push((now, earlier, full));
                        }
                    }
                }
            }
        }
        assert_eq!(
            disagreements(&pairs, |now, earlier| now.continues_from(earlier)),
            0
        );
        assert!(
            pairs.iter().any(|(n, e, _)| n.continues_from(*e))
                && pairs.iter().any(|(n, e, _)| !n.continues_from(*e)),
            "the sweep holds pairs that continue and pairs that do not"
        );
        assert!(
            disagreements(&pairs, |now, earlier| earlier.generation < now.generation) > 0,
            "NEGATIVE CONTROL: without the id rule, another log continues"
        );
        assert!(
            disagreements(&pairs, |now, earlier| earlier.id == now.id
                && earlier.generation <= now.generation)
                > 0,
            "NEGATIVE CONTROL: without the strict order, the same identity continues itself"
        );
    }

    /// Step lists for the `from_steps` sweep: EVERY list of up to four steps over
    /// generations {0, 1, 2, u64::MAX} (equal, falling and rising neighbours, the ends of
    /// the range), each with commons that rise, fall and sit at both ends; and, for every
    /// length up to two past [`Lineage::MAX`], the rising chain `1..=n` alone and with
    /// each neighbour made equal and made to fall — the only lists that reach the cap,
    /// since a small alphabet cannot rise that far.
    fn step_lists() -> Vec<Vec<(u64, u64)>> {
        const GENS: [u64; 4] = [0, 1, 2, u64::MAX];
        let commons = |i: usize| -> u64 {
            match i % 3 {
                0 => 0,
                1 => u64::MAX,
                _ => 7 - i as u64,
            }
        };
        let mut lists: Vec<Vec<(u64, u64)>> = vec![Vec::new()];
        let mut frontier: Vec<Vec<u64>> = vec![Vec::new()];
        for _ in 0..4 {
            let mut next = Vec::new();
            for gens in &frontier {
                for g in GENS {
                    let mut longer = gens.clone();
                    longer.push(g);
                    lists.push(
                        longer
                            .iter()
                            .enumerate()
                            .map(|(i, &g)| (g, commons(i)))
                            .collect(),
                    );
                    next.push(longer);
                }
            }
            frontier = next;
        }
        for n in 1..=Lineage::MAX + 2 {
            let chain: Vec<(u64, u64)> = (1..=n as u64).map(|g| (g, 100 - g)).collect();
            lists.push(chain.clone());
            for i in 1..n {
                let mut equal = chain.clone();
                equal[i].0 = equal[i - 1].0;
                lists.push(equal);
                let mut falling = chain.clone();
                falling[i].0 = 0;
                lists.push(falling);
            }
        }
        lists
    }

    /// The decoder's answer for `steps`: their wire form, built by hand from the layout
    /// the extension block's table documents (`n u8`, then `n × (generation u64 LE,
    /// common u64 LE)`) rather than by `Lineage::put`, read by `Lineage::from_wire` — the
    /// function every `Hello` answer's lineage entry goes through.
    fn decoded(steps: &[(u64, u64)]) -> Option<Lineage> {
        let mut wire = vec![u8::try_from(steps.len()).unwrap()];
        for &(g, c) in steps {
            wire.extend_from_slice(&g.to_le_bytes());
            wire.extend_from_slice(&c.to_le_bytes());
        }
        Lineage::from_wire(&wire)
    }

    /// `Lineage::from_steps` builds exactly the lineage the wire decoder reads from the
    /// same steps, and refuses exactly what the decoder refuses, over every list of
    /// [`step_lists`]: both of the decoder's rules are met (lists past the cap, lists whose
    /// generations do not rise) and so are lists it accepts, short and at the cap.
    ///
    /// Negative controls, on the same sweep: a constructor that skips the cap and one
    /// that skips the rising rule each disagree with the decoder, so the sweep reaches
    /// both rules and a `from_steps` that lost either would fail it.
    #[test]
    fn from_steps_agrees_with_the_decoder() {
        /// How many of `lists` `build` answers otherwise than the decoder.
        fn disagreements(
            lists: &[Vec<(u64, u64)>],
            build: impl Fn(&[(u64, u64)]) -> Option<Lineage>,
        ) -> usize {
            lists
                .iter()
                .filter(|steps| build(steps) != decoded(steps))
                .count()
        }
        let lists = step_lists();
        assert_eq!(disagreements(&lists, Lineage::from_steps), 0);
        let accepted = lists.iter().filter(|s| decoded(s).is_some()).count();
        assert!(
            accepted > 0 && accepted < lists.len(),
            "the sweep holds lists the decoder accepts and lists it refuses"
        );
        assert!(
            lists
                .iter()
                .any(|s| s.len() == Lineage::MAX && decoded(s).is_some()),
            "a lineage at the cap is accepted"
        );
        for steps in &lists {
            if let Some(l) = Lineage::from_steps(steps) {
                assert_eq!(l.steps(), &steps[..], "the steps, as given");
            }
        }

        let rises = |steps: &[(u64, u64)]| steps.windows(2).all(|w| w[0].0 < w[1].0);
        let uncapped = |steps: &[(u64, u64)]| {
            rises(steps).then(|| Lineage {
                steps: steps.to_vec(),
            })
        };
        let unordered = |steps: &[(u64, u64)]| {
            (steps.len() <= Lineage::MAX).then(|| Lineage {
                steps: steps.to_vec(),
            })
        };
        assert!(
            disagreements(&lists, uncapped) > 0,
            "NEGATIVE CONTROL: without the cap, a list past it is accepted"
        );
        assert!(
            disagreements(&lists, unordered) > 0,
            "NEGATIVE CONTROL: without the rising rule, a falling list is accepted"
        );
    }
}
