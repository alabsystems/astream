//! The broker wire protocol: each message is exactly one `astream_wire::Frame`
//! (inheriting CRC + the 16 MiB cap). The frame payload is a tiny tagged codec —
//! `| PROTO_VERSION:u8 | tag:u8 | body |`, every variable `u32` length
//! bounds-checked before slicing, the same fail-closed discipline as the engine
//! envelope. `read_frame`/`write_frame` are generic over `Read`/`Write`, so the
//! codec is unit-testable in memory with no socket.

use astream_wire::frame::{MAGIC as FRAME_MAGIC, VERSION as FRAME_VERSION};
use astream_wire::{crc32_ieee, Frame, FrameError, HEADER_SIZE, MAX_PAYLOAD_LEN};
use std::io::{self, Read, Write};

/// Protocol version (the payload's first byte).
pub const PROTO_VERSION: u8 = 2;

const TAG_PUBLISH: u8 = 0x01;
const TAG_SUBSCRIBE: u8 = 0x02;
const TAG_FORK_SUBSCRIBE: u8 = 0x03;
const TAG_COMMIT: u8 = 0x04;
const TAG_PROCESS: u8 = 0x05;
const TAG_SUBSCRIBE_GROUP: u8 = 0x06;
const TAG_ATTACH: u8 = 0x07;
const TAG_REPLICATE: u8 = 0x08;
const TAG_LAST: u8 = 0x09;
const TAG_FETCH: u8 = 0x0A;
const TAG_WILL: u8 = 0x0B;
const TAG_HELLO: u8 = 0x0C;
const TAG_ACK: u8 = 0x81;
const TAG_DELIVERY: u8 = 0x82;
const TAG_ERROR: u8 = 0x83;
const TAG_MARK: u8 = 0x84;
const TAG_NONCE: u8 = 0x85;

/// A client → broker request.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Request {
    /// Append `body` to `subject`, deduped by `(producer_id, producer_seq)`.
    Publish {
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
    },
    /// Stream every record matching `filter` from `from_offset`, then tail live.
    Subscribe { from_offset: u64, filter: String },
    /// COUNTERFACTUAL fork-delivery: stream the alternate timeline that results from
    /// forking the log at `fork_at` and swapping that one record for
    /// `(replacement_subject, replacement_body)`, filtered by `filter`. The live log
    /// is untouched (a sandbox view); delivery is the frozen counterfactual snapshot.
    ForkSubscribe {
        fork_at: u64,
        replacement_subject: String,
        replacement_body: Vec<u8>,
        filter: String,
    },
    /// Durably advance consumer `group`'s committed offset to `upto` (a pure commit).
    Commit { group: String, upto: u64 },
    /// The read-process-write TRANSACTION: append `out_body` to `out_subject` AND
    /// commit `group` to `upto` atomically (one durable record), deduped by
    /// `(producer_id, producer_seq)` — exactly-once processing.
    ProcessAndProduce {
        producer_id: u64,
        producer_seq: u64,
        out_subject: String,
        out_body: Vec<u8>,
        group: String,
        upto: u64,
    },
    /// Subscribe as consumer `group`: deliver matching records from the group's
    /// durable committed offset (broker-enforced resume), then tail live.
    SubscribeGroup { group: String, filter: String },
    /// Add a capability to this connection's KEYRING. `grant` is the signed grant
    /// string (`[rw|ro][,p=<principal>]:<filter>`, or a bare filter for the
    /// read-write unbound form); `proof` is a PROOF OF POSSESSION —
    /// `HMAC-SHA256(tag, nonce ‖ grant)` over the nonce this connection got from
    /// [`Request::Hello`] — so the capability's tag never crosses the wire and a
    /// captured `Attach` frame cannot be replayed onto another connection.
    ///
    /// It APPENDS (a repeated grant string replaces; the ring is bounded), and it is
    /// ACKNOWLEDGED with a [`Response::Mark`] — a rejected attach is visible at once
    /// rather than only at the next request. An unguarded broker acknowledges it and
    /// enforces nothing.
    Attach { grant: String, proof: Vec<u8> },
    /// REPLICATION (leader → follower): append this record at EXACTLY leader offset
    /// `seq`, with its producer key, subject, body, and any consumer-group commit
    /// annotation — so a follower's log is an identical prefix of the leader's
    /// (commit records and annotations included). Idempotent: a record already held
    /// at `seq` acks `deduped = true`; a gap, or a different record at `seq`, is
    /// refused (never silently overwritten). Acked like a publish.
    Replicate {
        seq: u64,
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
        /// `Some((group, upto))` for a commit-carrying record.
        commit: Option<(String, u64)>,
    },
    /// LAST-VALUE (retained state): deliver the most recent record of EVERY subject
    /// matching `filter` whose subject sorts strictly after `after` (`""` for the
    /// first page), at most `max` of them, in ascending SUBJECT order — then a
    /// [`Response::Mark`] carrying the head the page was read with. Non-terminal: the
    /// connection stays usable, so `Subscribe { from_offset: mark.next, filter }` on
    /// the same connection tails on gap-free from THAT page's snapshot. Each page of a
    /// PAGED query is read at its own, later head, so a paged reader tails from the
    /// FIRST page's `next` and folds newest-wins across the pages — tailing from the
    /// last page's `next` skips whatever superseded a value an earlier page reported.
    ///
    /// BOTH bounds are the BROKER's, not the client's: `max` is clamped to
    /// `LAST_PAGE_MAX` and the scan of the subject index is cut off after
    /// `LAST_SCAN_MAX` entries VISITED, matched or not. So the page may be shorter
    /// than `max` for a reason that is not "the answer ended", and the closing
    /// `Mark`'s `resume` is the cursor that continues it: page until `resume` is
    /// empty, passing it back as `after`, or the answer is silently truncated.
    Last {
        filter: String,
        after: String,
        max: u32,
    },
    /// BOUNDED, NON-TERMINAL read: deliver at most `max` records matching `filter`
    /// with offset >= `from_offset`, scanning at most `FETCH_SCAN_MAX` records — then
    /// a [`Response::Mark`] whose `next` is the offset after the LAST SCANNED record,
    /// so a sparse filter still advances the cursor instead of re-scanning. `max = 0`
    /// delivers nothing and is the head query. Unlike `Subscribe` it never tails and
    /// never ends the connection.
    Fetch {
        from_offset: u64,
        filter: String,
        max: u32,
    },
    /// REGISTER A LAST WILL: the record the broker appends ON THIS CONNECTION'S
    /// BEHALF when the connection ends, for any reason. Persisted first (a hidden
    /// `/a/will` record) and acknowledged with a [`Response::Mark`]; one per
    /// connection, a second replacing the first — under the SAME producer id, which is
    /// the only shape the durable record can express, so a second `Will` naming a
    /// DIFFERENT producer id is refused rather than silently leaving two wills on the
    /// log for the next broker open to fire.
    ///
    /// It fires as an ORDINARY publish under `(producer_id, producer_seq)`, so it is
    /// deduped like any other — a graceful goodbye that publishes the same key first
    /// makes the will a no-op — and it is FENCED: it appends nothing if a record with
    /// a HIGHER `producer_seq` from the same producer has since landed, which is how
    /// a reconnected producer structurally suppresses its previous incarnation's will.
    Will {
        producer_id: u64,
        producer_seq: u64,
        subject: String,
        body: Vec<u8>,
    },
    /// Open the capability handshake: ask for this connection's fresh
    /// [`Response::Nonce`], which an [`Attach`](Request::Attach)'s proof is computed
    /// over. Always allowed (it grants nothing); a guarded broker refuses an `Attach`
    /// with no preceding `Hello`.
    Hello,
}

/// A broker → client response.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Response {
    /// A publish landed (or deduped) at `offset`.
    PublishAck { offset: u64, deduped: bool },
    /// One delivered record.
    Delivery {
        offset: u64,
        subject: String,
        body: Vec<u8>,
    },
    /// The request was rejected (bad subject/filter/oversize/internal).
    Error { code: u8, msg: String },
    /// The end of a bounded, NON-TERMINAL read: `next` is the offset to resume from
    /// (a `Subscribe`/`Fetch` cursor) and `head` is the subscriber-visible head the
    /// answer was read with. Also the acknowledgement of an `Attach`.
    ///
    /// `resume` is the SUBJECT cursor of a [`Request::Last`] page: pass it back as
    /// `after` for the next page, and an EMPTY `resume` means the scan reached the end
    /// of the filter's range — this was the last page. It is empty on every other
    /// verb's `Mark` (`Fetch` pages by offset through `next`; `Attach` and `Will`
    /// carry no cursor at all).
    ///
    /// `resume` is not an optional trailer. A broker that predates the field stamps
    /// payload byte 0 with its own `PROTO_VERSION`, and [`decode_response`] refuses
    /// the frame at that byte, so a `Mark` that ends after `head` is a current peer's
    /// frame cut short: it decodes as malformed like every other short body (read as
    /// `resume = ""` it would report "this was the last page" for a truncated answer).
    Mark {
        next: u64,
        head: u64,
        resume: String,
    },
    /// This connection's fresh nonce (32 bytes), the answer to
    /// [`Request::Hello`]. An `Attach`'s proof is `HMAC-SHA256(tag, nonce ‖ grant)`
    /// over it, which binds the attach to THIS connection.
    Nonce { nonce: Vec<u8> },
}

fn put_str(p: &mut Vec<u8>, s: &str) {
    p.extend_from_slice(&(s.len() as u32).to_le_bytes());
    p.extend_from_slice(s.as_bytes());
}
fn put_bytes(p: &mut Vec<u8>, b: &[u8]) {
    p.extend_from_slice(&(b.len() as u32).to_le_bytes());
    p.extend_from_slice(b);
}

struct Reader<'a> {
    b: &'a [u8],
    i: usize,
}
impl<'a> Reader<'a> {
    fn u8(&mut self) -> Option<u8> {
        let v = *self.b.get(self.i)?;
        self.i += 1;
        Some(v)
    }
    fn u64(&mut self) -> Option<u64> {
        let end = self.i.checked_add(8)?;
        let v = u64::from_le_bytes(self.b.get(self.i..end)?.try_into().ok()?);
        self.i = end;
        Some(v)
    }
    fn u32(&mut self) -> Option<usize> {
        let end = self.i.checked_add(4)?;
        let v = u32::from_le_bytes(self.b.get(self.i..end)?.try_into().ok()?) as usize;
        self.i = end;
        Some(v)
    }
    fn take(&mut self, n: usize) -> Option<Vec<u8>> {
        let end = self.i.checked_add(n)?;
        let v = self.b.get(self.i..end)?.to_vec();
        self.i = end;
        Some(v)
    }
    fn string(&mut self) -> Option<String> {
        let n = self.u32()?;
        String::from_utf8(self.take(n)?).ok()
    }
    fn bytes(&mut self) -> Option<Vec<u8>> {
        let n = self.u32()?;
        self.take(n)
    }
}

/// Encode a request to a frame payload.
pub fn encode_request(req: &Request) -> Vec<u8> {
    let mut p = vec![PROTO_VERSION, 0];
    match req {
        Request::Publish {
            producer_id,
            producer_seq,
            subject,
            body,
        } => {
            p[1] = TAG_PUBLISH;
            p.extend_from_slice(&producer_id.to_le_bytes());
            p.extend_from_slice(&producer_seq.to_le_bytes());
            put_str(&mut p, subject);
            put_bytes(&mut p, body);
        }
        Request::Subscribe {
            from_offset,
            filter,
        } => {
            p[1] = TAG_SUBSCRIBE;
            p.extend_from_slice(&from_offset.to_le_bytes());
            put_str(&mut p, filter);
        }
        Request::ForkSubscribe {
            fork_at,
            replacement_subject,
            replacement_body,
            filter,
        } => {
            p[1] = TAG_FORK_SUBSCRIBE;
            p.extend_from_slice(&fork_at.to_le_bytes());
            put_str(&mut p, replacement_subject);
            put_bytes(&mut p, replacement_body);
            put_str(&mut p, filter);
        }
        Request::Commit { group, upto } => {
            p[1] = TAG_COMMIT;
            put_str(&mut p, group);
            p.extend_from_slice(&upto.to_le_bytes());
        }
        Request::ProcessAndProduce {
            producer_id,
            producer_seq,
            out_subject,
            out_body,
            group,
            upto,
        } => {
            p[1] = TAG_PROCESS;
            p.extend_from_slice(&producer_id.to_le_bytes());
            p.extend_from_slice(&producer_seq.to_le_bytes());
            put_str(&mut p, out_subject);
            put_bytes(&mut p, out_body);
            put_str(&mut p, group);
            p.extend_from_slice(&upto.to_le_bytes());
        }
        Request::SubscribeGroup { group, filter } => {
            p[1] = TAG_SUBSCRIBE_GROUP;
            put_str(&mut p, group);
            put_str(&mut p, filter);
        }
        Request::Attach { grant, proof } => {
            p[1] = TAG_ATTACH;
            put_str(&mut p, grant);
            put_bytes(&mut p, proof);
        }
        Request::Will {
            producer_id,
            producer_seq,
            subject,
            body,
        } => {
            p[1] = TAG_WILL;
            p.extend_from_slice(&producer_id.to_le_bytes());
            p.extend_from_slice(&producer_seq.to_le_bytes());
            put_str(&mut p, subject);
            put_bytes(&mut p, body);
        }
        Request::Hello => p[1] = TAG_HELLO,
        Request::Replicate {
            seq,
            producer_id,
            producer_seq,
            subject,
            body,
            commit,
        } => {
            return encode_replicate(
                *seq,
                *producer_id,
                *producer_seq,
                subject,
                body,
                commit.as_ref().map(|(g, u)| (g.as_str(), *u)),
            );
        }
        Request::Last { filter, after, max } => {
            p[1] = TAG_LAST;
            put_str(&mut p, filter);
            put_str(&mut p, after);
            p.extend_from_slice(&max.to_le_bytes());
        }
        Request::Fetch {
            from_offset,
            filter,
            max,
        } => {
            p[1] = TAG_FETCH;
            p.extend_from_slice(&from_offset.to_le_bytes());
            put_str(&mut p, filter);
            p.extend_from_slice(&max.to_le_bytes());
        }
    }
    p
}

/// Encode a `Replicate` payload directly from BORROWED fields — the leader's
/// replication path ships shared `Arc`'d log records without cloning subject/body
/// into a `Request` first. Byte-identical to `encode_request(&Request::Replicate {..})`.
pub fn encode_replicate(
    seq: u64,
    producer_id: u64,
    producer_seq: u64,
    subject: &str,
    body: &[u8],
    commit: Option<(&str, u64)>,
) -> Vec<u8> {
    let mut p = vec![PROTO_VERSION, TAG_REPLICATE];
    p.extend_from_slice(&seq.to_le_bytes());
    p.extend_from_slice(&producer_id.to_le_bytes());
    p.extend_from_slice(&producer_seq.to_le_bytes());
    put_str(&mut p, subject);
    put_bytes(&mut p, body);
    match commit {
        None => p.push(0),
        Some((group, upto)) => {
            p.push(1);
            put_str(&mut p, group);
            p.extend_from_slice(&upto.to_le_bytes());
        }
    }
    p
}

/// Decode a request from a frame payload (bounds-checked; `None` on malformed).
pub fn decode_request(p: &[u8]) -> Option<Request> {
    let mut r = Reader { b: p, i: 0 };
    if r.u8()? != PROTO_VERSION {
        return None;
    }
    match r.u8()? {
        TAG_PUBLISH => Some(Request::Publish {
            producer_id: r.u64()?,
            producer_seq: r.u64()?,
            subject: r.string()?,
            body: r.bytes()?,
        }),
        TAG_SUBSCRIBE => Some(Request::Subscribe {
            from_offset: r.u64()?,
            filter: r.string()?,
        }),
        TAG_FORK_SUBSCRIBE => Some(Request::ForkSubscribe {
            fork_at: r.u64()?,
            replacement_subject: r.string()?,
            replacement_body: r.bytes()?,
            filter: r.string()?,
        }),
        TAG_COMMIT => Some(Request::Commit {
            group: r.string()?,
            upto: r.u64()?,
        }),
        TAG_PROCESS => Some(Request::ProcessAndProduce {
            producer_id: r.u64()?,
            producer_seq: r.u64()?,
            out_subject: r.string()?,
            out_body: r.bytes()?,
            group: r.string()?,
            upto: r.u64()?,
        }),
        TAG_SUBSCRIBE_GROUP => Some(Request::SubscribeGroup {
            group: r.string()?,
            filter: r.string()?,
        }),
        TAG_ATTACH => Some(Request::Attach {
            grant: r.string()?,
            proof: r.bytes()?,
        }),
        TAG_WILL => Some(Request::Will {
            producer_id: r.u64()?,
            producer_seq: r.u64()?,
            subject: r.string()?,
            body: r.bytes()?,
        }),
        TAG_HELLO => Some(Request::Hello),
        TAG_REPLICATE => {
            let seq = r.u64()?;
            let producer_id = r.u64()?;
            let producer_seq = r.u64()?;
            let subject = r.string()?;
            let body = r.bytes()?;
            let commit = match r.u8()? {
                0 => None,
                1 => Some((r.string()?, r.u64()?)),
                _ => return None,
            };
            Some(Request::Replicate {
                seq,
                producer_id,
                producer_seq,
                subject,
                body,
                commit,
            })
        }
        TAG_LAST => Some(Request::Last {
            filter: r.string()?,
            after: r.string()?,
            max: r.u32()? as u32,
        }),
        TAG_FETCH => Some(Request::Fetch {
            from_offset: r.u64()?,
            filter: r.string()?,
            max: r.u32()? as u32,
        }),
        _ => None,
    }
}

/// Encode a response to a frame payload.
pub fn encode_response(resp: &Response) -> Vec<u8> {
    let mut p = vec![PROTO_VERSION, 0];
    match resp {
        Response::PublishAck { offset, deduped } => {
            p[1] = TAG_ACK;
            p.extend_from_slice(&offset.to_le_bytes());
            p.push(*deduped as u8);
        }
        Response::Delivery {
            offset,
            subject,
            body,
        } => {
            p[1] = TAG_DELIVERY;
            p.extend_from_slice(&offset.to_le_bytes());
            put_str(&mut p, subject);
            put_bytes(&mut p, body);
        }
        Response::Error { code, msg } => {
            p[1] = TAG_ERROR;
            p.push(*code);
            put_str(&mut p, msg);
        }
        Response::Mark { next, head, resume } => {
            p[1] = TAG_MARK;
            p.extend_from_slice(&next.to_le_bytes());
            p.extend_from_slice(&head.to_le_bytes());
            put_str(&mut p, resume);
        }
        Response::Nonce { nonce } => {
            p[1] = TAG_NONCE;
            put_bytes(&mut p, nonce);
        }
    }
    p
}

/// Encode a `Delivery` payload directly from BORROWED fields — the egress hot path.
/// Byte-identical to `encode_response(&Response::Delivery { offset, subject, body })`,
/// but it does not construct/own a `Response`, so a shared `Arc`'d log record's subject
/// and body are read by reference (no deep copy on the read path; the only copy is the
/// one unavoidable assembly into the outgoing frame).
pub fn encode_delivery(offset: u64, subject: &str, body: &[u8]) -> Vec<u8> {
    let mut p = Vec::with_capacity(2 + 8 + 4 + subject.len() + 4 + body.len());
    put_delivery(&mut p, offset, subject, body);
    p
}

fn put_delivery(p: &mut Vec<u8>, offset: u64, subject: &str, body: &[u8]) {
    p.extend_from_slice(&[PROTO_VERSION, TAG_DELIVERY]);
    p.extend_from_slice(&offset.to_le_bytes());
    put_str(p, subject);
    put_bytes(p, body);
}

/// Append one framed `Delivery` to `out`, assembled in place: the body is copied once,
/// into `out`, instead of into a payload, then a `Frame`, then the encoded frame. A
/// streaming verb gathers several into one buffer and writes them with one call.
pub(crate) fn append_delivery_frame(
    out: &mut Vec<u8>,
    offset: u64,
    subject: &str,
    body: &[u8],
) -> io::Result<()> {
    append_framed(out, |p| put_delivery(p, offset, subject, body))
}

/// Append `payload`, framed, to `out` (one copy). See [`append_delivery_frame`].
pub(crate) fn append_frame(out: &mut Vec<u8>, payload: &[u8]) -> io::Result<()> {
    append_framed(out, |p| p.extend_from_slice(payload))
}

/// Frame, in place, the payload `fill` appends to `out`: the header is reserved first
/// and written once the payload's length and CRC are known. Byte-identical to
/// `Frame::new(payload).encode()`. A payload over the cap leaves `out` as it was and
/// is `InvalidData`.
fn append_framed(out: &mut Vec<u8>, fill: impl FnOnce(&mut Vec<u8>)) -> io::Result<()> {
    let start = out.len();
    out.resize(start + HEADER_SIZE, 0);
    fill(out);
    let len = out.len() - start - HEADER_SIZE;
    let Some(len32) = u32::try_from(len).ok().filter(|_| len <= MAX_PAYLOAD_LEN) else {
        out.truncate(start);
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "payload exceeds cap",
        ));
    };
    let crc = crc32_ieee(&out[start + HEADER_SIZE..]);
    let hdr = &mut out[start..start + HEADER_SIZE];
    hdr[..2].copy_from_slice(&FRAME_MAGIC);
    hdr[2] = FRAME_VERSION;
    hdr[3] = 0; // flags: none defined
    hdr[4..8].copy_from_slice(&len32.to_le_bytes());
    hdr[8..].copy_from_slice(&crc.to_le_bytes());
    Ok(())
}

/// Decode a response from a frame payload (bounds-checked; `None` on malformed).
pub fn decode_response(p: &[u8]) -> Option<Response> {
    let mut r = Reader { b: p, i: 0 };
    if r.u8()? != PROTO_VERSION {
        return None;
    }
    match r.u8()? {
        TAG_ACK => Some(Response::PublishAck {
            offset: r.u64()?,
            deduped: r.u8()? != 0,
        }),
        TAG_DELIVERY => Some(Response::Delivery {
            offset: r.u64()?,
            subject: r.string()?,
            body: r.bytes()?,
        }),
        TAG_ERROR => Some(Response::Error {
            code: r.u8()?,
            msg: r.string()?,
        }),
        TAG_MARK => Some(Response::Mark {
            next: r.u64()?,
            head: r.u64()?,
            // NOT optional. An older broker is refused at the version byte above, so a
            // Mark that ends after `head` is a current peer's truncated frame, and an
            // empty `resume` means something specific ("the scan reached the end of the
            // filter's range") that a truncation must not be read as.
            resume: r.string()?,
        }),
        TAG_NONCE => Some(Response::Nonce { nonce: r.bytes()? }),
        _ => None,
    }
}

/// Bytes of a frame's payload read per `read_exact` call: a frame's buffer GROWS as its
/// bytes arrive rather than being allocated at the declared length up front, so a peer
/// that announces a 16 MiB frame and then stalls pins one chunk (plus what it actually
/// sent) until its read times out — not the whole declared length.
const READ_CHUNK: usize = 64 * 1024;

/// Read exactly one frame's payload from `r` (blocking). `Ok(None)` on a clean EOF
/// (peer closed at a frame boundary); `Err` on a malformed/oversized frame, or
/// `UnexpectedEof` on a frame cut short — in its header or its payload. `read_exact`
/// handles partial reads (it loops until each chunk arrives).
pub fn read_frame(r: &mut impl Read) -> io::Result<Option<Vec<u8>>> {
    let mut hdr = [0u8; HEADER_SIZE];
    // The first read decides between a clean close (nothing at all) and a frame;
    // once any header byte has arrived, a short header is a truncated frame.
    let first = loop {
        match r.read(&mut hdr) {
            Ok(n) => break n,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    };
    if first == 0 {
        return Ok(None);
    }
    r.read_exact(&mut hdr[first..])?;
    // The header is judged BEFORE the payload it announces is read: a bad magic,
    // version or flags byte, or a length over the cap, is refused on these 12 bytes.
    // A header on its own decodes as "need more bytes" — or, announcing an empty
    // payload, as the whole frame.
    match Frame::decode(&hdr) {
        Ok(None) => {}
        Ok(Some(d)) => return Ok(Some(d.frame.payload)),
        Err(FrameError::TooLarge) => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "frame exceeds cap",
            ))
        }
        Err(_) => return Err(io::Error::new(io::ErrorKind::InvalidData, "corrupt frame")),
    }
    let len = u32::from_le_bytes([hdr[4], hdr[5], hdr[6], hdr[7]]) as usize;
    let crc = u32::from_le_bytes([hdr[8], hdr[9], hdr[10], hdr[11]]);
    // Read straight into the payload buffer (no header copy, no second copy out).
    let mut payload = Vec::with_capacity(len.min(READ_CHUNK));
    while payload.len() < len {
        let start = payload.len();
        payload.resize(start + (len - start).min(READ_CHUNK), 0);
        r.read_exact(&mut payload[start..])?;
    }
    if crc32_ieee(&payload) != crc {
        return Err(io::Error::new(io::ErrorKind::InvalidData, "corrupt frame"));
    }
    Ok(Some(payload))
}

/// Frame `payload` and write it to `w` (blocking), in one `write_all`.
pub fn write_frame(w: &mut impl Write, payload: &[u8]) -> io::Result<()> {
    let mut out = Vec::with_capacity(HEADER_SIZE + payload.len());
    append_frame(&mut out, payload)?;
    w.write_all(&out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn requests_round_trip() {
        let p = Request::Publish {
            producer_id: 9,
            producer_seq: 4,
            subject: "/a/stream/x".into(),
            body: b"hi".to_vec(),
        };
        assert_eq!(decode_request(&encode_request(&p)), Some(p));
        let s = Request::Subscribe {
            from_offset: 7,
            filter: "/a/stream/>".into(),
        };
        assert_eq!(decode_request(&encode_request(&s)), Some(s));
    }

    #[test]
    fn replicate_round_trips_with_and_without_a_commit() {
        let plain = Request::Replicate {
            seq: 11,
            producer_id: 3,
            producer_seq: 4,
            subject: "/a/r/x".into(),
            body: b"m".to_vec(),
            commit: None,
        };
        assert_eq!(decode_request(&encode_request(&plain)), Some(plain.clone()));
        let with_commit = Request::Replicate {
            seq: 11,
            producer_id: 3,
            producer_seq: 4,
            subject: "/a/r/x".into(),
            body: b"m".to_vec(),
            commit: Some(("g1".to_string(), 10)),
        };
        let bytes = encode_request(&with_commit);
        assert_eq!(decode_request(&bytes), Some(with_commit));
        // The borrowed-field encoder is byte-identical to the Request encoder.
        assert_eq!(
            encode_replicate(11, 3, 4, "/a/r/x", b"m", Some(("g1", 10))),
            bytes
        );
        // An unknown commit tag byte is malformed, not misread.
        let mut bad = encode_replicate(1, 1, 1, "/a/x", b"", None);
        *bad.last_mut().unwrap() = 2;
        assert_eq!(decode_request(&bad), None);
    }

    /// A reader that hands out at most `step` bytes per call — the shape of a socket
    /// delivering a large frame in pieces.
    struct Trickle<'a> {
        bytes: &'a [u8],
        step: usize,
    }
    impl std::io::Read for Trickle<'_> {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            let n = self.bytes.len().min(self.step).min(buf.len());
            buf[..n].copy_from_slice(&self.bytes[..n]);
            self.bytes = &self.bytes[n..];
            Ok(n)
        }
    }

    /// A frame larger than one read chunk is assembled chunk by chunk (from a reader
    /// that trickles it) byte-identically, and a frame cut short mid-payload is
    /// `UnexpectedEof`, never a partial payload.
    #[test]
    fn large_frames_are_read_in_chunks_and_a_short_one_is_unexpected_eof() {
        let payload: Vec<u8> = (0..(3 * READ_CHUNK + 17))
            .map(|i| (i % 251) as u8)
            .collect();
        let mut wire = Vec::new();
        write_frame(&mut wire, &payload).unwrap();
        let mut trickle = Trickle {
            bytes: &wire,
            step: 1000,
        };
        assert_eq!(read_frame(&mut trickle).unwrap(), Some(payload));
        assert_eq!(
            read_frame(&mut trickle).unwrap(),
            None,
            "clean EOF after the frame"
        );
        let mut short = Trickle {
            bytes: &wire[..wire.len() - 5],
            step: 4096,
        };
        assert_eq!(
            read_frame(&mut short).unwrap_err().kind(),
            io::ErrorKind::UnexpectedEof
        );
    }

    /// Only a stream that ends exactly at a frame boundary is a clean close. One cut
    /// short INSIDE the 12-byte header is `UnexpectedEof`, like one cut inside its
    /// payload — a subscriber must not read a broker that died mid-header as a
    /// stream that ended.
    #[test]
    fn a_frame_cut_inside_its_header_is_unexpected_eof() {
        let mut wire = Vec::new();
        write_frame(&mut wire, b"payload").unwrap();
        for cut in 1..HEADER_SIZE {
            let mut short = Trickle {
                bytes: &wire[..cut],
                step: 4096,
            };
            assert_eq!(
                read_frame(&mut short).map_err(|e| e.kind()),
                Err(io::ErrorKind::UnexpectedEof),
                "header cut after {cut} bytes"
            );
        }
        let mut empty = Trickle {
            bytes: &[],
            step: 4096,
        };
        assert_eq!(read_frame(&mut empty).unwrap(), None);
    }

    /// The in-place framer is byte-identical to the wire crate's `Frame::encode`, a
    /// framed delivery to `encode_delivery` framed, and an over-cap payload is refused
    /// leaving the buffer as it was.
    #[test]
    fn in_place_framing_matches_frame_encode() {
        for payload in [&b""[..], b"x", &[7u8; 70_000]] {
            let mut out = b"prefix".to_vec();
            append_frame(&mut out, payload).unwrap();
            assert_eq!(&out[..6], b"prefix");
            assert_eq!(out[6..], Frame::new(payload.to_vec()).encode().unwrap()[..]);
        }
        let mut out = Vec::new();
        append_delivery_frame(&mut out, 9, "/a/x", b"body").unwrap();
        assert_eq!(
            out,
            Frame::new(encode_delivery(9, "/a/x", b"body"))
                .encode()
                .unwrap()
        );
        let mut out = b"kept".to_vec();
        let big = vec![0u8; MAX_PAYLOAD_LEN + 1];
        assert_eq!(
            append_frame(&mut out, &big).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
        assert_eq!(out, b"kept");
    }

    /// A header that announces a frame the reader must refuse is refused on the header
    /// alone: the reader never waits for (or buffers) the payload it announces.
    #[test]
    fn a_bad_header_is_refused_before_its_payload_is_read() {
        let mut wire = Vec::new();
        write_frame(&mut wire, &[1u8; 32]).unwrap();
        // Bad magic, over-cap length: only the 12 header bytes are available.
        let mut bad_magic = wire[..HEADER_SIZE].to_vec();
        bad_magic[0] ^= 0xFF;
        let mut over_cap = wire[..HEADER_SIZE].to_vec();
        over_cap[4..8].copy_from_slice(&(MAX_PAYLOAD_LEN as u32 + 1).to_le_bytes());
        for hdr in [bad_magic, over_cap] {
            let mut r = Trickle {
                bytes: &hdr,
                step: 4096,
            };
            assert_eq!(
                read_frame(&mut r).unwrap_err().kind(),
                io::ErrorKind::InvalidData
            );
        }
        // A flipped payload byte is still caught by the CRC.
        let mut corrupt = wire.clone();
        *corrupt.last_mut().unwrap() ^= 1;
        let mut r = Trickle {
            bytes: &corrupt,
            step: 4096,
        };
        assert_eq!(
            read_frame(&mut r).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
    }

    #[test]
    fn responses_round_trip() {
        let a = Response::PublishAck {
            offset: 3,
            deduped: true,
        };
        assert_eq!(decode_response(&encode_response(&a)), Some(a));
        let d = Response::Delivery {
            offset: 5,
            subject: "/a/stream/x".into(),
            body: b"body".to_vec(),
        };
        assert_eq!(decode_response(&encode_response(&d)), Some(d));
    }

    #[test]
    fn frame_round_trip_in_memory_and_clean_eof() {
        let mut buf = Vec::new();
        write_frame(
            &mut buf,
            &encode_request(&Request::Subscribe {
                from_offset: 0,
                filter: "/a/>".into(),
            }),
        )
        .unwrap();
        let mut cur = std::io::Cursor::new(buf);
        let payload = read_frame(&mut cur).unwrap().unwrap();
        assert!(matches!(
            decode_request(&payload),
            Some(Request::Subscribe { .. })
        ));
        // No more bytes => clean EOF.
        assert_eq!(read_frame(&mut cur).unwrap(), None);
    }

    /// PROTOCOL ECONOMY, PINNED. The whole fabric —
    /// retained values, bounded reads, a last will, a proof-of-possession attach, an
    /// exactly-once inbox, request/reply, barriers and presence — rides on TWELVE
    /// request tags and FIVE response tags. This test is the budget: it enumerates
    /// every byte and fails if a thirteenth request tag or a sixth response tag ever
    /// decodes, and it pins each tag's NUMBER, so a renumbering that would silently
    /// re-interpret an old client's frames breaks the build instead.
    #[test]
    fn the_tag_budget_is_twelve_requests_and_five_responses() {
        // Version 2: `Attach` kept its tag (0x07) and its wire SHAPE (a str then a
        // byte string) while its MEANING changed (`{grant, proof}`, answered with a
        // Mark), so under an unchanged version byte a version-1 Attach would decode
        // CLEANLY into the new variant. The byte is checked on every decode, which
        // turns that silent reinterpretation into a refusal. The stored format is
        // unaffected.
        assert_eq!(
            PROTO_VERSION, 2,
            "PROTO_VERSION moved to 2 with Attach's redefinition"
        );
        assert_eq!(
            crate::brecord::BREC_VERSION,
            2,
            "the stored record format stays 2: nothing here is an on-disk change"
        );

        // Every tag's NUMBER, pinned against the variant that carries it.
        let request_tags: [(u8, Request); 12] = [
            (
                0x01,
                Request::Publish {
                    producer_id: 0,
                    producer_seq: 0,
                    subject: String::new(),
                    body: Vec::new(),
                },
            ),
            (
                0x02,
                Request::Subscribe {
                    from_offset: 0,
                    filter: String::new(),
                },
            ),
            (
                0x03,
                Request::ForkSubscribe {
                    fork_at: 0,
                    replacement_subject: String::new(),
                    replacement_body: Vec::new(),
                    filter: String::new(),
                },
            ),
            (
                0x04,
                Request::Commit {
                    group: String::new(),
                    upto: 0,
                },
            ),
            (
                0x05,
                Request::ProcessAndProduce {
                    producer_id: 0,
                    producer_seq: 0,
                    out_subject: String::new(),
                    out_body: Vec::new(),
                    group: String::new(),
                    upto: 0,
                },
            ),
            (
                0x06,
                Request::SubscribeGroup {
                    group: String::new(),
                    filter: String::new(),
                },
            ),
            (
                0x07,
                Request::Attach {
                    grant: String::new(),
                    proof: Vec::new(),
                },
            ),
            (
                0x08,
                Request::Replicate {
                    seq: 0,
                    producer_id: 0,
                    producer_seq: 0,
                    subject: String::new(),
                    body: Vec::new(),
                    commit: None,
                },
            ),
            (
                0x09,
                Request::Last {
                    filter: String::new(),
                    after: String::new(),
                    max: 0,
                },
            ),
            (
                0x0A,
                Request::Fetch {
                    from_offset: 0,
                    filter: String::new(),
                    max: 0,
                },
            ),
            (
                0x0B,
                Request::Will {
                    producer_id: 0,
                    producer_seq: 0,
                    subject: String::new(),
                    body: Vec::new(),
                },
            ),
            (0x0C, Request::Hello),
        ];
        for (tag, req) in &request_tags {
            let bytes = encode_request(req);
            assert_eq!(bytes[1], *tag, "tag number moved for {req:?}");
            assert_eq!(
                decode_request(&bytes).as_ref(),
                Some(req),
                "round trip for tag {tag:#04x}"
            );
        }

        let response_tags: [(u8, Response); 5] = [
            (
                0x81,
                Response::PublishAck {
                    offset: 0,
                    deduped: false,
                },
            ),
            (
                0x82,
                Response::Delivery {
                    offset: 0,
                    subject: String::new(),
                    body: Vec::new(),
                },
            ),
            (
                0x83,
                Response::Error {
                    code: 0,
                    msg: String::new(),
                },
            ),
            (
                0x84,
                Response::Mark {
                    next: 0,
                    head: 0,
                    resume: String::new(),
                },
            ),
            (0x85, Response::Nonce { nonce: Vec::new() }),
        ];
        for (tag, resp) in &response_tags {
            let bytes = encode_response(resp);
            assert_eq!(bytes[1], *tag, "tag number moved for {resp:?}");
            assert_eq!(
                decode_response(&bytes).as_ref(),
                Some(resp),
                "round trip for tag {tag:#04x}"
            );
        }

        // THE BUDGET: sweep every byte. A zero-filled body satisfies every declared
        // tag's parser (empty strings, empty byte vectors, a `None` commit), so a tag
        // decodes here IF AND ONLY IF it is declared — an undeclared byte is `None`,
        // which is what keeps an old broker's answer to a new client `Error 5,
        // "malformed request"` and nothing else.
        let mut body = vec![PROTO_VERSION, 0];
        body.extend_from_slice(&[0u8; 64]);
        let declared_requests: Vec<u8> = request_tags.iter().map(|(t, _)| *t).collect();
        let declared_responses: Vec<u8> = response_tags.iter().map(|(t, _)| *t).collect();
        let mut decodable_requests = Vec::new();
        let mut decodable_responses = Vec::new();
        for tag in 0u8..=255 {
            body[1] = tag;
            if decode_request(&body).is_some() {
                decodable_requests.push(tag);
            }
            if decode_response(&body).is_some() {
                decodable_responses.push(tag);
            }
        }
        assert_eq!(
            decodable_requests, declared_requests,
            "exactly twelve request tags decode, and no other byte does"
        );
        assert_eq!(
            decodable_responses, declared_responses,
            "exactly five response tags decode, and no other byte does"
        );

        // And the version byte still gates every tag, response tags included: the
        // right tag under the wrong version decodes to nothing at all. The body is
        // the same zero-filled one the sweep just proved every declared tag's parser
        // accepts, so what refuses these frames is the version byte — not a body that
        // ran out early.
        body[0] = PROTO_VERSION + 1;
        for tag in &declared_requests {
            body[1] = *tag;
            assert_eq!(
                decode_request(&body),
                None,
                "request tag {tag:#04x} decoded under a wrong version byte"
            );
        }
        for tag in &declared_responses {
            body[1] = *tag;
            assert_eq!(
                decode_response(&body),
                None,
                "response tag {tag:#04x} decoded under a wrong version byte"
            );
        }
    }

    #[test]
    fn malformed_payload_decodes_to_none() {
        assert_eq!(decode_request(&[]), None);
        assert_eq!(decode_request(&[PROTO_VERSION, TAG_PUBLISH, 1, 2]), None);
        assert_eq!(decode_request(&[9, TAG_PUBLISH]), None); // bad version
    }

    /// A `Mark` that stops after `head` is MALFORMED, not an older broker's frame: an
    /// older broker is refused at the version byte, so tolerating the short form would
    /// only read a current peer's truncated page as `resume = ""` — "the scan reached
    /// the end of the filter's range".
    #[test]
    fn a_mark_truncated_after_head_is_malformed() {
        let full = encode_response(&Response::Mark {
            next: 4,
            head: 9,
            resume: "/f/x".to_string(),
        });
        assert_eq!(
            decode_response(&full),
            Some(Response::Mark {
                next: 4,
                head: 9,
                resume: "/f/x".to_string()
            })
        );
        // The 18-byte prefix: version, tag, next, head, and nothing more.
        assert_eq!(
            decode_response(&full[..18]),
            None,
            "a short Mark is malformed"
        );
        // An older broker does not get this far: its version byte is refused.
        let mut older = full.clone();
        older[0] = PROTO_VERSION - 1;
        assert_eq!(decode_response(&older), None);
    }
}
