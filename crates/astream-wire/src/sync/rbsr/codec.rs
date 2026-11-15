// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Frame bounds limit one allocation, never the total inventory. Lists and actor
//! frontiers continue in as many frames as required. The integrating transport
//! carries these bytes as one length-bounded message.

use super::{Digest, Error, Fingerprint, Frontier, Range};

/// Maximum encoded frame size, checked before decoding or allocating its lists.
pub const MAX_FRAME_BYTES: usize = 8192;
/// At most this many identities or actor anchors in one continuing list frame.
pub const PAGE: usize = 64;

/// A compact probe is only a hint. Completion uses the full root fingerprints;
/// a conservation mismatch requires full-width refinement of skipped ranges.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Probe {
    /// Record count and low 32 bits of the digest sum.
    Compact(u64, [u8; 4]),
    /// Complete count and 256-bit digest sum.
    Full(Fingerprint),
}

impl Probe {
    /// Choose a full or compact probe from the same complete local summary.
    #[must_use]
    pub fn new(fingerprint: Fingerprint, full: bool) -> Self {
        if full {
            Self::Full(fingerprint)
        } else {
            let (count, tag) = fingerprint.probe();
            Self::Compact(count, tag)
        }
    }

    /// Whether this probe agrees with the local range summary.
    #[must_use]
    pub fn matches(self, fingerprint: Fingerprint) -> bool {
        match self {
            Self::Full(expected) => expected == fingerprint,
            Self::Compact(count, tag) => (count, tag) == fingerprint.probe(),
        }
    }
}

/// One transport-independent step. A receiver must additionally hold the message
/// to its current protocol phase and the exact outstanding request.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Message {
    /// Full inventory summary, never a compact completion check.
    Root(Fingerprint),
    /// Dense actor anchors, strictly increasing within and across continuing pages.
    Frontiers { items: Vec<Frontier>, done: bool },
    /// Independently proven shared prefixes, with the same paging rule.
    Prefixes { items: Vec<Frontier>, done: bool },
    /// Initiator's sixteen child summaries for this nonterminal range.
    Split {
        range: Range,
        children: Box<[Probe; 16]>,
    },
    /// Responder's unequal-child mask and counts at exactly those child positions.
    SplitReply {
        range: Range,
        different: u16,
        counts: [u64; 16],
    },
    /// Read one sorted identity page in this range, strictly after the cursor.
    ListRequest { range: Range, after: Option<Digest> },
    /// A page responding to the exact range and cursor the receiver requested.
    List {
        range: Range,
        ids: Vec<Digest>,
        done: bool,
    },
    /// Difference identities, sorted across continuing pages. `local_only`
    /// identifies the initiator's send set; `false` identifies its want set.
    Difference {
        ids: Vec<Digest>,
        done: bool,
        local_only: bool,
    },
    /// Full contributions removed from the two original inventory summaries.
    Finish {
        local_only: Fingerprint,
        remote_only: Fingerprint,
    },
    /// Refine compact-probe omissions with complete 256-bit child summaries.
    Refine,
    /// Acceptance of a difference page or refinement request.
    Accepted,
}

impl Message {
    /// Encode one canonical bounded message.
    /// # Errors
    /// [`Error::Wire`] for oversized, unordered or inconsistent fields, or a
    /// terminal range submitted for splitting.
    pub fn encode(&self) -> Result<Vec<u8>, Error> {
        let mut out = b"AR1".to_vec();
        match self {
            Self::Root(fingerprint) => {
                out.push(0);
                put_fingerprint(&mut out, *fingerprint)?;
            }
            Self::Frontiers { items, done } | Self::Prefixes { items, done } => {
                if items.len() > PAGE
                    || (!done && items.is_empty())
                    || items.windows(2).any(|pair| pair[0].actor >= pair[1].actor)
                    || items.iter().any(|item| item.sequence == 0)
                {
                    return Err(Error::Wire);
                }
                out.push(if matches!(self, Self::Frontiers { .. }) {
                    1
                } else {
                    2
                });
                out.push(u8::from(*done));
                out.push(items.len() as u8);
                for item in items {
                    out.extend_from_slice(&item.actor);
                    put_count(&mut out, item.sequence);
                    out.extend_from_slice(&item.id);
                }
            }
            Self::Split { range, children } => {
                if range.children().is_none() {
                    return Err(Error::Wire);
                }
                out.push(3);
                put_range(&mut out, *range);
                for child in children.iter() {
                    match child {
                        Probe::Compact(count, tag) => {
                            if *count == 0 && *tag != [0; 4] {
                                return Err(Error::Wire);
                            }
                            out.push(0);
                            put_count(&mut out, *count);
                            if *count != 0 {
                                out.extend_from_slice(tag);
                            }
                        }
                        Probe::Full(fingerprint) => {
                            out.push(1);
                            put_fingerprint(&mut out, *fingerprint)?;
                        }
                    }
                }
            }
            Self::SplitReply {
                range,
                different,
                counts,
            } => {
                if range.children().is_none() {
                    return Err(Error::Wire);
                }
                out.push(4);
                put_range(&mut out, *range);
                out.extend_from_slice(&different.to_le_bytes());
                for (position, count) in counts.iter().enumerate() {
                    if different & (1 << position) != 0 {
                        put_count(&mut out, *count);
                    } else if *count != 0 {
                        return Err(Error::Wire);
                    }
                }
            }
            Self::ListRequest { range, after } => {
                if after.is_some_and(|id| !range.contains(&id)) {
                    return Err(Error::Wire);
                }
                out.push(5);
                put_range(&mut out, *range);
                out.push(u8::from(after.is_some()));
                if let Some(id) = after {
                    out.extend_from_slice(id);
                }
            }
            Self::List { range, ids, done } => {
                out.push(6);
                put_range(&mut out, *range);
                put_ids(&mut out, ids, *done, *range)?;
            }
            Self::Difference {
                ids,
                done,
                local_only,
            } => {
                out.push(7);
                out.push(u8::from(*local_only));
                put_ids(&mut out, ids, *done, Range::ROOT)?;
            }
            Self::Finish {
                local_only,
                remote_only,
            } => {
                out.push(8);
                put_fingerprint(&mut out, *local_only)?;
                put_fingerprint(&mut out, *remote_only)?;
            }
            Self::Refine => out.push(9),
            Self::Accepted => out.push(10),
        }
        if out.len() > MAX_FRAME_BYTES {
            return Err(Error::Wire);
        }
        Ok(out)
    }

    /// Decode exactly one bounded message. Trailing bytes are refused.
    /// # Errors
    /// [`Error::Wire`] or [`Error::Range`] for malformed, noncanonical, truncated
    /// or oversized input. No list allocates beyond [`PAGE`] elements.
    pub fn decode(bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() > MAX_FRAME_BYTES {
            return Err(Error::Wire);
        }
        let mut input = Reader { bytes, at: 0 };
        if input.take::<3>()? != *b"AR1" {
            return Err(Error::Wire);
        }
        let message = match input.byte()? {
            0 => Self::Root(input.fingerprint()?),
            tag @ (1 | 2) => {
                let done = input.boolean()?;
                let count = usize::from(input.byte()?);
                if count > PAGE || (!done && count == 0) {
                    return Err(Error::Wire);
                }
                let mut items = Vec::with_capacity(count);
                for _ in 0..count {
                    let item = Frontier {
                        actor: input.take()?,
                        sequence: input.count()?,
                        id: input.take()?,
                    };
                    if item.sequence == 0
                        || items
                            .last()
                            .is_some_and(|last: &Frontier| last.actor >= item.actor)
                    {
                        return Err(Error::Wire);
                    }
                    items.push(item);
                }
                if tag == 1 {
                    Self::Frontiers { items, done }
                } else {
                    Self::Prefixes { items, done }
                }
            }
            3 => {
                let range = input.range()?;
                if range.children().is_none() {
                    return Err(Error::Wire);
                }
                let mut children = Box::new([Probe::Compact(0, [0; 4]); 16]);
                for child in children.iter_mut() {
                    *child = match input.byte()? {
                        0 => {
                            let count = input.count()?;
                            let tag = if count == 0 { [0; 4] } else { input.take()? };
                            Probe::Compact(count, tag)
                        }
                        1 => Probe::Full(input.fingerprint()?),
                        _ => return Err(Error::Wire),
                    };
                }
                Self::Split { range, children }
            }
            4 => {
                let range = input.range()?;
                if range.children().is_none() {
                    return Err(Error::Wire);
                }
                let different = u16::from_le_bytes(input.take()?);
                let mut counts = [0; 16];
                for (position, count) in counts.iter_mut().enumerate() {
                    if different & (1 << position) != 0 {
                        *count = input.count()?;
                    }
                }
                Self::SplitReply {
                    range,
                    different,
                    counts,
                }
            }
            5 => {
                let range = input.range()?;
                let after = if input.boolean()? {
                    Some(input.take()?)
                } else {
                    None
                };
                if after.is_some_and(|id| !range.contains(&id)) {
                    return Err(Error::Wire);
                }
                Self::ListRequest { range, after }
            }
            6 => {
                let range = input.range()?;
                let (ids, done) = input.ids(range)?;
                Self::List { range, ids, done }
            }
            7 => {
                let local_only = input.boolean()?;
                let (ids, done) = input.ids(Range::ROOT)?;
                Self::Difference {
                    ids,
                    done,
                    local_only,
                }
            }
            8 => Self::Finish {
                local_only: input.fingerprint()?,
                remote_only: input.fingerprint()?,
            },
            9 => Self::Refine,
            10 => Self::Accepted,
            _ => return Err(Error::Wire),
        };
        if input.at != bytes.len() {
            return Err(Error::Wire);
        }
        Ok(message)
    }
}

fn put_count(out: &mut Vec<u8>, mut value: u64) {
    while value >= 128 {
        out.push((value as u8) | 128);
        value >>= 7;
    }
    out.push(value as u8);
}

fn put_fingerprint(out: &mut Vec<u8>, value: Fingerprint) -> Result<(), Error> {
    if value.count == 0 && value.sum != [0; 32] {
        return Err(Error::Wire);
    }
    put_count(out, value.count);
    if value.count != 0 {
        out.extend_from_slice(&value.sum);
    }
    Ok(())
}

fn put_range(out: &mut Vec<u8>, range: Range) {
    let (prefix, depth) = range.prefix();
    out.push(depth);
    out.extend_from_slice(&prefix[..usize::from(depth).div_ceil(2)]);
}

fn put_ids(out: &mut Vec<u8>, ids: &[Digest], done: bool, range: Range) -> Result<(), Error> {
    if ids.len() > PAGE
        || (!done && ids.is_empty())
        || ids.windows(2).any(|pair| pair[0] >= pair[1])
        || ids.iter().any(|id| !range.contains(id))
    {
        return Err(Error::Wire);
    }
    out.push(u8::from(done));
    out.push(ids.len() as u8);
    for id in ids {
        out.extend_from_slice(id);
    }
    Ok(())
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl Reader<'_> {
    fn take<const N: usize>(&mut self) -> Result<[u8; N], Error> {
        let end = self.at.checked_add(N).ok_or(Error::Wire)?;
        let bytes = self.bytes.get(self.at..end).ok_or(Error::Wire)?;
        let value = bytes.try_into().map_err(|_| Error::Wire)?;
        self.at = end;
        Ok(value)
    }

    fn byte(&mut self) -> Result<u8, Error> {
        Ok(self.take::<1>()?[0])
    }

    fn boolean(&mut self) -> Result<bool, Error> {
        match self.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(Error::Wire),
        }
    }

    fn count(&mut self) -> Result<u64, Error> {
        let mut value = 0;
        for group in 0..10 {
            let byte = self.byte()?;
            if group == 9 && byte > 1 {
                return Err(Error::Wire);
            }
            value |= u64::from(byte & 127) << (7 * group);
            if byte < 128 {
                if group != 0 && byte == 0 {
                    return Err(Error::Wire);
                }
                return Ok(value);
            }
        }
        Err(Error::Wire)
    }

    fn fingerprint(&mut self) -> Result<Fingerprint, Error> {
        let count = self.count()?;
        let value = Fingerprint {
            count,
            sum: if count == 0 { [0; 32] } else { self.take()? },
        };
        Ok(value)
    }

    fn range(&mut self) -> Result<Range, Error> {
        let depth = self.byte()?;
        if depth > 64 {
            return Err(Error::Range);
        }
        let length = usize::from(depth).div_ceil(2);
        let end = self.at.checked_add(length).ok_or(Error::Wire)?;
        let bytes = self.bytes.get(self.at..end).ok_or(Error::Wire)?;
        let mut prefix = [0; 32];
        prefix[..length].copy_from_slice(bytes);
        self.at = end;
        Range::new(prefix, depth)
    }

    fn ids(&mut self, range: Range) -> Result<(Vec<Digest>, bool), Error> {
        let done = self.boolean()?;
        let count = usize::from(self.byte()?);
        if count > PAGE || (!done && count == 0) {
            return Err(Error::Wire);
        }
        let mut ids = Vec::with_capacity(count);
        for _ in 0..count {
            let id = self.take()?;
            if !range.contains(&id) || ids.last().is_some_and(|last| *last >= id) {
                return Err(Error::Wire);
            }
            ids.push(id);
        }
        Ok((ids, done))
    }
}

#[cfg(test)]
#[path = "codec_tests.rs"]
mod tests;
