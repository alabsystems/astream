// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! THE OPEN'S STREAMING SCAN: the log read through a bounded WINDOW, each record handed on
//! as it is decoded and then forgotten, and the records of the tier's hot window read again
//! once the scan has decided it ([`decode_run`]).
//!
//! Before it the open read the whole log into one buffer, decoded every record of it into a
//! vector, freed the buffer after the scan and only then let the residency tier apply its
//! budget, so a broker's restart held the file and every record decoded at once: on a sealed
//! log of about 1.02M records (aterm F09) the open peaked at 584.8 MB where the broker
//! serves at 44 to 47.
//!
//! The scan here reads the file a window at a time ([`WINDOW`] bytes, more only for a frame
//! longer than that, which is at most a header and `MAX_PAYLOAD_LEN`), judges each frame as
//! the whole-buffer scan judged it ([`step`], held to the reference `scan_from` by
//! `open_scan_tests.rs`), and hands each record it accepts to a [`Sink`]: the open's fold
//! into the residency tier and its indices (`OpenFold`), or nothing at all for the check that
//! writes nothing (`check_open.rs`).
//!
//! WHAT A VERDICT READS. A frame that decodes is judged by its header and the payload its
//! header announces alone (`astream_wire::frame::validate_frame_at`), which the window holds
//! whole before it is judged, so that verdict is the one the whole buffer gave. A frame that
//! STOPS the scan (torn, damaged, unreadable here, or in a newer format) is judged by every
//! byte from it to the end of the file as well (whether those are all zeros, whether an
//! intact record follows: `later_record_exists`), and so is the recovery after it
//! (`recover::classify`, which reads [`Streamed::rest`]). So a scan that stops before the
//! window reaches the end of the file reads the rest of it whole, judges the frame again on
//! that, and hands the window's own buffer on as the rest, so those bytes are held once. A
//! clean log stops only at its end, where that rest is empty; a torn tail's rest is the frame
//! a crash cut short.

use std::fs::File;
use std::io;

use astream_wire::{Frame, HEADER_SIZE, MAX_PAYLOAD_LEN};

use super::{
    all_zero_bytes, later_record_exists, open_disk_payload, AtRestRef, Mutation, RepairAt, Scan,
    Tail,
};
use crate::brecord::{BrokerRecord, Mark};
use crate::storage::Backing;

/// The bytes the scan's window reads at a time.
pub(crate) const WINDOW: usize = 4 << 20;

/// Where the scan reads the log: bytes by position.
pub(crate) trait ReadAt {
    /// Up to `buf.len()` bytes from byte `at`, fewer only where the log ends: how many.
    fn read_some_at(&self, at: u64, buf: &mut [u8]) -> io::Result<usize>;

    /// The log's length in bytes (an open holds the log's lock, so it stays this long).
    fn byte_len(&self) -> io::Result<u64>;
}

impl ReadAt for Backing {
    fn read_some_at(&self, at: u64, buf: &mut [u8]) -> io::Result<usize> {
        Backing::read_some_at(self, at, buf)
    }

    fn byte_len(&self) -> io::Result<u64> {
        Backing::len(self)
    }
}

impl ReadAt for File {
    fn read_some_at(&self, at: u64, buf: &mut [u8]) -> io::Result<usize> {
        crate::storage::read_some_at(self, buf, at)
    }

    fn byte_len(&self) -> io::Result<u64> {
        crate::storage::file_len(self)
    }
}

/// A log held whole in memory (a test's).
#[cfg(test)]
impl ReadAt for [u8] {
    fn read_some_at(&self, at: u64, buf: &mut [u8]) -> io::Result<usize> {
        let from = usize::try_from(at).unwrap_or(usize::MAX);
        let have = self.get(from..).unwrap_or(&[]);
        let n = have.len().min(buf.len());
        if let (Some(dst), Some(src)) = (buf.get_mut(..n), have.get(..n)) {
            dst.copy_from_slice(src);
        }
        Ok(n)
    }

    fn byte_len(&self) -> io::Result<u64> {
        Ok(self.len() as u64)
    }
}

/// What the scan hands each record of the intact prefix to, in offset order.
pub(crate) trait Sink {
    /// Record `rec`, its broker time `bt`, its frame `frame` as stored starting at byte
    /// `at`; `ends_unit`: it ends a unit ([`Mark::ends_a_unit`]), so a recovery never cuts
    /// below it. `false` ends the scan after it.
    fn record(
        &mut self,
        rec: BrokerRecord,
        bt: Option<u64>,
        at: u64,
        frame: &[u8],
        ends_unit: bool,
    ) -> bool;
}

/// The sink that keeps nothing: the check that writes nothing (`check_open.rs`) judges the
/// prefix by the scan alone.
pub(crate) struct Discard;

impl Sink for Discard {
    fn record(&mut self, _: BrokerRecord, _: Option<u64>, _: u64, _: &[u8], _: bool) -> bool {
        true
    }
}

/// How the scan reads the log: its window's size and, in a test, a negative control.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Reading {
    /// The bytes the window reads at a time ([`WINDOW`] in a shipped open).
    pub(crate) window: usize,
    /// The negative control: a record whose frame straddles the window's end is passed
    /// over, never handed to the sink.
    #[cfg(test)]
    pub(crate) drop_straddle: bool,
}

impl Reading {
    /// The shipped open's.
    pub(crate) const fn shipped() -> Reading {
        Reading {
            window: WINDOW,
            #[cfg(test)]
            drop_straddle: false,
        }
    }
}

/// What the streaming scan found.
pub(crate) struct Streamed {
    pub(crate) scan: Scan,
    /// The stored bytes from the end of the intact prefix to the end of the file, which the
    /// recovery judges (`recover::Judge::rest`): empty when the prefix reaches the end.
    pub(crate) rest: Vec<u8>,
}

/// The scan's verdict on one frame.
enum Step {
    /// The next record of the intact prefix, its mark, its broker time, and the bytes its
    /// frame takes.
    Record {
        rec: BrokerRecord,
        mark: Mark,
        bt: Option<u64>,
        consumed: usize,
    },
    /// The intact prefix ends here, as `Tail` says.
    Stop(Tail),
}

/// The scan's verdict on the frame `rest` starts with, at byte `pos`, where record
/// `expected` is due: the reference `scan_from`'s, frame by frame. `rest` holds that frame
/// whole (its header and the payload the header announces) or every byte to the end of the
/// file; a [`Step::Stop`] is final only on the second.
fn step(
    rest: &[u8],
    key: Option<AtRestRef<'_>>,
    expected: u64,
    pos: usize,
    mutation: Mutation,
) -> Step {
    if rest.is_empty() {
        return Step::Stop(Tail::Clean);
    }
    match Frame::decode(rest) {
        // An EMPTY frame is never a record: the reference scan says why.
        Ok(Some(d)) if d.frame.payload.is_empty() && !mutation.no_empty_frame_rule() => {
            if all_zero_bytes(rest) {
                return Step::Stop(Tail::Torn);
            }
            Step::Stop(Tail::Corrupt {
                offset: expected,
                at_byte: pos,
                reason: "an empty frame: a torn header, or damage".to_string(),
                repair_at: RepairAt::Cut,
                tear: true,
            })
        }
        Ok(Some(d)) => {
            let consumed = d.consumed;
            let Some(payload) = open_disk_payload(key, expected, d.frame.payload) else {
                return Step::Stop(Tail::Corrupt {
                    offset: expected,
                    at_byte: pos,
                    reason:
                        "record failed to authenticate (wrong at-rest key or a tampered record)"
                            .to_string(),
                    repair_at: RepairAt::WrongKey,
                    tear: false,
                });
            };
            match BrokerRecord::from_payload_marked_bt(&payload) {
                Some((r, _, _)) if r.seq.0 == u64::MAX => Step::Stop(Tail::Corrupt {
                    offset: expected,
                    at_byte: pos,
                    reason: "record at offset u64::MAX, which the log never assigns".to_string(),
                    repair_at: RepairAt::Cut,
                    tear: false,
                }),
                Some((rec, mark, bt)) if rec.seq.0 == expected => Step::Record {
                    rec,
                    mark,
                    bt,
                    consumed,
                },
                Some((r, _, _)) => Step::Stop(Tail::Corrupt {
                    offset: expected,
                    at_byte: pos,
                    reason: format!("offset gap: expected seq {expected}, found {}", r.seq.0),
                    repair_at: RepairAt::Cut,
                    tear: false,
                }),
                None => {
                    if let Some(version) = crate::brecord::newer_format(&payload, Some(expected)) {
                        return Step::Stop(Tail::Newer {
                            offset: expected,
                            at_byte: pos,
                            version,
                        });
                    }
                    if key.is_none() && pos == 0 {
                        return Step::Stop(Tail::Corrupt {
                            offset: expected,
                            at_byte: pos,
                            reason:
                                "the log's first record is intact (its CRC holds) but is not a \
                                 plaintext record: a log sealed at rest, read without its key, \
                                 or a record format this build does not read"
                                    .to_string(),
                            repair_at: RepairAt::NeedsKey,
                            tear: false,
                        });
                    }
                    Step::Stop(Tail::Corrupt {
                        offset: expected,
                        at_byte: pos,
                        reason:
                            "record payload does not parse (an older BREC_VERSION, or malformed)"
                                .to_string(),
                        repair_at: RepairAt::Cut,
                        tear: false,
                    })
                }
            }
        }
        Ok(None) => {
            let raw_key = match key {
                Some(k) => Some(k.key),
                None => None,
            };
            if later_record_exists(rest, raw_key) {
                return Step::Stop(Tail::Corrupt {
                    offset: expected,
                    at_byte: pos,
                    reason: "frame claims to extend past the end of the log but intact records \
                         follow it (a corrupt length field, not a torn write)"
                        .to_string(),
                    repair_at: RepairAt::Cut,
                    tear: true,
                });
            }
            Step::Stop(Tail::Torn)
        }
        Err(e) => {
            if all_zero_bytes(rest) {
                return Step::Stop(Tail::Torn);
            }
            Step::Stop(Tail::Corrupt {
                offset: expected,
                at_byte: pos,
                reason: format!("frame does not decode: {e}"),
                repair_at: RepairAt::Cut,
                tear: true,
            })
        }
    }
}

/// The payload length a frame header announces (its `u32` at bytes 4..8, the layout
/// `astream_wire::frame` documents), when `bytes` holds a whole header.
fn announced(bytes: &[u8]) -> Option<usize> {
    let hdr = bytes.first_chunk::<HEADER_SIZE>()?;
    let len = u32::from_le_bytes([hdr[4], hdr[5], hdr[6], hdr[7]]);
    usize::try_from(len).ok()
}

/// The bytes of the log the scan holds: `buf` is the file from byte `at`.
struct Window {
    buf: Vec<u8>,
    at: usize,
    /// `buf` runs to the end of the file.
    end: bool,
    /// The bytes it reads at a time.
    size: usize,
    /// The file's length when the scan began: no read reaches past it, so a log shorter than
    /// a window costs only its own bytes.
    len: usize,
}

impl Window {
    fn new(size: usize, len: usize) -> Window {
        Window {
            buf: Vec::new(),
            at: 0,
            end: len == 0,
            size: size.max(1),
            len,
        }
    }

    /// The bytes held from byte `pos` (empty below the window or past what it holds).
    fn from(&self, pos: usize) -> &[u8] {
        match pos.checked_sub(self.at) {
            Some(k) => self.buf.get(k..).unwrap_or(&[]),
            None => &[],
        }
    }

    /// Hold `n` bytes from byte `pos` (`pos` at or after the window's start), or every byte
    /// to the end of the file: the bytes before `pos` are let go first, and the reads are at
    /// least a window's worth. Whether it read.
    fn need(&mut self, src: &(impl ReadAt + ?Sized), pos: usize, n: usize) -> io::Result<bool> {
        if self.end || self.from(pos).len() >= n {
            return Ok(false);
        }
        let passed = pos.saturating_sub(self.at).min(self.buf.len());
        vec_drop_prefix(&mut self.buf, passed);
        self.at = pos;
        let want = n.max(self.size).min(self.len.saturating_sub(pos));
        if self.buf.len() >= want {
            self.end = true;
        }
        let mut scratch = [0u8; 65_536];
        while self.buf.len() < want && !self.end {
            let old = self.buf.len();
            let step = want.saturating_sub(old).min(scratch.len());
            let at = self.at.saturating_add(old) as u64;
            let got = match scratch.get_mut(..step) {
                Some(spare) => src.read_some_at(at, spare)?,
                None => 0,
            };
            if let Some(read_bytes) = scratch.get(..got) {
                self.buf.extend_from_slice(read_bytes);
            }
            if got == 0 || (self.buf.len() >= want && pos.saturating_add(want) >= self.len) {
                self.end = true;
            }
        }
        // A frame longer than a window grew the buffer; give that back once it is passed.
        if self.buf.capacity() > self.size.saturating_mul(2) && self.buf.len() <= self.size {
            self.buf.shrink_to(self.size);
        }
        Ok(true)
    }

    /// Hold the frame at byte `pos` whole — its header and the payload its header announces —
    /// or every byte to the end of the file. Whether the frame straddled the window's end: the
    /// window held part of it and read the rest.
    fn frame_at(&mut self, src: &(impl ReadAt + ?Sized), pos: usize) -> io::Result<bool> {
        let held = !self.from(pos).is_empty();
        let mut read = self.need(src, pos, HEADER_SIZE)?;
        if let Some(len) = announced(self.from(pos)) {
            if len <= MAX_PAYLOAD_LEN {
                read |= self.need(src, pos, HEADER_SIZE.saturating_add(len))?;
            }
        }
        Ok(held && read)
    }

    /// Hold every byte from `pos` to the end of the file.
    fn hold_to_end(&mut self, src: &(impl ReadAt + ?Sized), pos: usize) -> io::Result<()> {
        while !self.end {
            let more = self.from(pos).len().saturating_add(self.size);
            self.need(src, pos, more)?;
        }
        Ok(())
    }

    /// The bytes held from byte `pos` ([`from`](Self::from)) as the window's own buffer, the
    /// bytes before them let go in place: a scan that stopped before the end of the file holds
    /// the rest once ([`hold_to_end`](Self::hold_to_end)), never beside a copy of it. Cut to
    /// what it holds when that is under half the buffer: a torn tail's rest is a few bytes of
    /// a window's worth.
    fn into_rest(self, pos: usize) -> Vec<u8> {
        let Some(skip) = pos.checked_sub(self.at) else {
            return Vec::new();
        };
        let mut buf = self.buf;
        vec_drop_prefix(&mut buf, skip);
        if buf.len() < buf.capacity() / 2 {
            buf.shrink_to_fit();
        }
        buf
    }
}

fn vec_drop_prefix<T>(v: &mut Vec<T>, k: usize) {
    let len = v.len();
    let drop_n = k.min(len);
    if drop_n == 0 {
        return;
    }
    let keep = len.saturating_sub(drop_n);
    for idx in 0..keep {
        let src = idx.saturating_add(drop_n);
        if let Some(sub) = v.get_mut(idx..=src) {
            if let Some((first, rest)) = sub.split_first_mut() {
                if let Some(end) = rest.last_mut() {
                    std::mem::swap(first, end);
                }
            }
        }
    }
    v.truncate(keep);
}

/// THE OPEN'S SCAN of the log `src` holds: the longest intact, in-order prefix of records
/// from `base`, each handed to `sink` as it is decoded, its byte length, and how the bytes end
/// — the reference `scan_from`'s answer, through a window of `reading.window` bytes. A scan
/// its sink ends reports the prefix it passed, ending cleanly.
pub(crate) fn scan(
    src: &(impl ReadAt + ?Sized),
    reading: Reading,
    key: Option<AtRestRef<'_>>,
    base: u64,
    floor: Option<u64>,
    mutation: Mutation,
    sink: &mut impl Sink,
) -> io::Result<Streamed> {
    let Ok(len) = usize::try_from(src.byte_len()?) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "a log longer than memory",
        ));
    };
    let mut win = Window::new(reading.window, len);
    let mut count = 0usize;
    let mut pos = 0usize;
    let mut seal_end = (base, 0usize);
    let mut floor_at = if floor == Some(base) {
        Some(0usize)
    } else {
        None
    };
    let tail = loop {
        let expected = base.saturating_add(count as u64);
        let straddled = win.frame_at(src, pos)?;
        let rest = win.from(pos);
        match step(rest, key, expected, pos, mutation) {
            Step::Record {
                rec,
                mark,
                bt,
                consumed,
            } => {
                #[cfg(test)]
                if reading.drop_straddle && straddled && consumed > 0 {
                    pos = pos.saturating_add(consumed);
                    continue;
                }
                let _ = straddled;
                let frame = rest.get(..consumed).unwrap_or(rest);
                count = count.saturating_add(1);
                let more = sink.record(rec, bt, pos as u64, frame, mark.ends_a_unit());
                // A decoded frame always consumes at least its header; guard anyway so a
                // zero-progress decode can never spin.
                if consumed == 0 {
                    break Tail::Corrupt {
                        offset: expected,
                        at_byte: pos,
                        reason: "zero-length frame".to_string(),
                        repair_at: RepairAt::Cut,
                        tear: false,
                    };
                }
                pos = pos.saturating_add(consumed);
                if mark.ends_a_unit() {
                    seal_end = (expected.saturating_add(1), pos);
                }
                if floor == Some(expected.saturating_add(1)) {
                    floor_at = Some(pos);
                }
                if !more {
                    break Tail::Clean;
                }
            }
            Step::Stop(tail) => {
                if win.end {
                    break tail;
                }
                // Judged on the bytes to the end of the file, as the whole buffer judged it.
                win.hold_to_end(src, pos)?;
            }
        }
    };
    let rest = if matches!(tail, Tail::Clean) {
        Vec::new()
    } else {
        win.into_rest(pos)
    };
    Ok(Streamed {
        scan: Scan {
            count,
            valid_len: pos,
            tail,
            seal_end,
            floor_at,
        },
        rest,
    })
}

/// The log's first stored frame as stored — header and the payload its header announces,
/// unchecked ([`logid::first_frame`](crate::logid::first_frame)'s answer on the whole log) —
/// read from `src`, whose length is `len`: `None` when the log ends before it.
pub(crate) fn first_frame(src: &(impl ReadAt + ?Sized), len: u64) -> io::Result<Option<Vec<u8>>> {
    let mut hdr = [0u8; HEADER_SIZE];
    if src.read_some_at(0, &mut hdr)? < HEADER_SIZE {
        return Ok(None);
    }
    let Some(payload) = announced(&hdr) else {
        return Ok(None);
    };
    if payload > MAX_PAYLOAD_LEN {
        return Ok(None);
    }
    let whole = HEADER_SIZE.saturating_add(payload);
    if (whole as u64) > len || whole > HEADER_SIZE + MAX_PAYLOAD_LEN {
        return Ok(None);
    }
    let mut frame = vec![0u8; whole];
    let got = src.read_some_at(0, &mut frame)?;
    frame.truncate(got);
    Ok(crate::logid::first_frame(&frame).map(<[u8]>::to_vec))
}

/// The stored frame (header and payload, as stored) that starts at byte `at` of `src`: a
/// record of the intact prefix the scan accepted.
pub(crate) fn frame_at(src: &(impl ReadAt + ?Sized), at: u64) -> io::Result<Vec<u8>> {
    let mut hdr = [0u8; HEADER_SIZE];
    let short = || io::Error::new(io::ErrorKind::UnexpectedEof, "a scanned frame reads short");
    if src.read_some_at(at, &mut hdr)? < HEADER_SIZE {
        return Err(short());
    }
    let payload = announced(&hdr).ok_or_else(short)?;
    if payload > MAX_PAYLOAD_LEN {
        return Err(short());
    }
    let whole = HEADER_SIZE.saturating_add(payload);
    if whole > HEADER_SIZE + MAX_PAYLOAD_LEN {
        return Err(short());
    }
    let mut frame = vec![0u8; whole];
    if src.read_some_at(at, &mut frame)? < frame.len() {
        return Err(short());
    }
    Ok(frame)
}

/// THE WINDOW READ AGAIN: the `count` records stored from byte `at` of `src` on, the first of
/// them record `first`, each decoded as the scan decoded it ([`step`], through a window of
/// `window` bytes) and handed to `each`. The open's scan lets a record go once it is folded,
/// and the tier's hot window is decided only by the records after it, so the records of that
/// window are read here once the scan has decided it ([`crate::tier::Opening::finish`]).
///
/// # Errors
///
/// A read's, `each`'s, and `InvalidData` for a record the scan accepted that reads otherwise
/// now.
pub(crate) fn decode_run(
    src: &(impl ReadAt + ?Sized),
    window: usize,
    key: Option<AtRestRef<'_>>,
    mutation: Mutation,
    (at, first, count): (u64, u64, usize),
    each: &mut dyn FnMut(BrokerRecord) -> io::Result<()>,
) -> io::Result<()> {
    let Ok(len) = usize::try_from(src.byte_len()?) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "a log longer than memory",
        ));
    };
    let Ok(mut pos) = usize::try_from(at) else {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "a frame past memory",
        ));
    };
    let mut win = Window::new(window, len);
    for i in 0..count {
        let expected = first.saturating_add(i as u64);
        win.frame_at(src, pos)?;
        match step(win.from(pos), key, expected, pos, mutation) {
            Step::Record { rec, consumed, .. } if consumed > 0 => {
                pos = pos.saturating_add(consumed);
                if let Some(r) = Some(()).map(|()| each(rec)) {
                    r?;
                }
            }
            Step::Record { .. } | Step::Stop(_) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!(
                        "record {expected} at byte {pos}, which the open's scan accepted, \
                         reads otherwise now"
                    ),
                ));
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A scan that stops short of the end of the file hands on, as the rest, the window's own
    /// buffer holding the bytes from where it stopped to the end, not a copy of them beside
    /// it: read to the end from there, or already holding the end with bytes before it.
    #[test]
    fn a_scan_that_stops_short_hands_on_the_buffer_it_read_to_the_end_as_its_rest() {
        let bytes: Vec<u8> = (0..100u8).collect();
        let src: &[u8] = &bytes;

        let mut win = Window::new(16, bytes.len());
        assert!(win.need(src, 0, HEADER_SIZE).unwrap());
        win.hold_to_end(src, 40).unwrap();
        assert!(win.end);
        let held = win.buf.as_ptr();
        let rest = win.into_rest(40);
        assert_eq!(rest, &bytes[40..]);
        assert_eq!(rest.as_ptr(), held, "the rest read to the end is a copy");

        let mut win = Window::new(256, bytes.len());
        assert!(win.need(src, 0, HEADER_SIZE).unwrap());
        assert!(win.end);
        let held = win.buf.as_ptr();
        let rest = win.into_rest(40);
        assert_eq!(rest, &bytes[40..]);
        assert_eq!(
            rest.as_ptr(),
            held,
            "the rest of a window that held the end is a copy"
        );

        // A few bytes of a large buffer are cut to what they hold.
        let mut win = Window::new(256, bytes.len());
        assert!(win.need(src, 0, HEADER_SIZE).unwrap());
        let rest = win.into_rest(97);
        assert_eq!(rest, &bytes[97..]);
        assert!(
            rest.capacity() < 50,
            "a 3-byte rest keeps {} bytes",
            rest.capacity()
        );

        // A stop before what the window holds has no rest to hand on.
        let mut win = Window::new(16, bytes.len());
        assert!(win.need(src, 50, HEADER_SIZE).unwrap());
        assert!(win.into_rest(40).is_empty());
    }
}
