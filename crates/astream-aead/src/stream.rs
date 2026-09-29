//! [`SealedStream`] — a transparent, ordered-record AEAD adapter over any
//! `Read + Write`, so an existing length-prefixed protocol becomes confidential
//! and authenticated with no change to the protocol code above it.
//!
//! # Handshake: session freshness and direction binding
//! A stream is opened with [`SealedStream::handshake_client`] on one end and
//! [`SealedStream::handshake_server`] on the other. Each side sends one HELLO in
//! the clear — [`HELLO_MAGIC`] ‖ [`SESSION_NONCE_LEN`] bytes from the OS CSPRNG —
//! then reads the peer's. Every record's AAD is then
//!
//! ```text
//! hello_client ‖ hello_server ‖ direction ‖ seq        (36 + 36 + 1 + 8 bytes)
//! ```
//!
//! with `direction` = 0x01 for client→server / 0x02 for server→client and `seq`
//! the per-direction record counter (u64 little-endian, from 0). Both hellos are
//! fresh per connection and one of them is always chosen by the honest side, so
//! a record is valid ONLY for this connection, this direction, and this
//! position: a record recorded from any other connection (either direction), a
//! record reflected back at its sender, and a record replayed, reordered,
//! dropped, or truncated within the connection all fail their tag. The
//! handshake ends with each side sending a CONFIRM — record 0 of its direction,
//! empty — that the peer must open before the handshake returns: key possession
//! and the hello transcript are confirmed before any application byte flows,
//! and a peer without the key is refused inside the handshake. The record key
//! is the pre-shared key itself; the `handshake` feature's key agreement, which
//! enters through [`SealedStream::with_transcript`], adds forward secrecy.
//!
//! # Framing
//! Each `write(buf)` seals `buf` into one or more records of at most
//! [`MAX_PLAINTEXT`] plaintext bytes each (a record ceiling, as in TLS) and
//! emits `len: u32-le ‖ nonce ‖ ciphertext ‖ tag` per record. Each `read`
//! drains from the currently-open record, opening the next on demand — so the
//! caller sees a plain byte stream and its own framing (the broker's `Frame`)
//! rides inside, blind to the record boundaries beneath it. An empty record is
//! skipped, never reported as EOF: `Ok(0)` from `read` means the peer closed at
//! a record boundary, exactly as the `Read` contract requires.
//!
//! # Bounds
//! A record whose length prefix exceeds [`MAX_RECORD`] is rejected before any of
//! it is read, so a hostile prefix pins at most `MAX_RECORD` bytes; under the
//! hello handshake the one record read before the peer has authenticated (its
//! confirm) is capped at exactly [`OVERHEAD`](crate::OVERHEAD) bytes, so an
//! unkeyed peer can make the reader allocate nothing beyond that. A partial or
//! timed-out transport read is resumed at the same record boundary by the next
//! `read`, never desynced. A write that fails after part of a record reached the
//! transport cannot be resumed that way, so it poisons the send side.
//!
//! Honest boundary: there is no close-notify record. A transport cut exactly at a
//! record boundary is indistinguishable from an orderly close (`read` returns
//! `Ok(0)`); a cut inside a record is truncation and errors. What an early EOF
//! means is decided by the protocol above, exactly as it is on a plain socket.
//!
//! # Shared counters across clones
//! The send and receive counters are shared (`Arc`) across
//! [`SealedStream::try_clone`], so a second handle to the same socket (the
//! broker's ack-writer half) keeps a single gap-free record sequence per
//! direction. A `write` seals all of its records under the send lock, so the
//! records of two handles never interleave within one write.

use crate::{open_in_place, seal_in_place, KEY_LEN, NONCE_LEN, OVERHEAD, TAG_LEN};
use std::io::{self, Read, Write};
use std::sync::{Arc, Mutex};

/// Largest plaintext one record carries; a longer `write` is split into several
/// records. Bounds the buffer a peer can make the reader hold per record.
pub const MAX_PLAINTEXT: usize = 64 * 1024;
/// Ceiling on a sealed record's on-wire length (`MAX_PLAINTEXT + OVERHEAD`); a
/// length prefix above it is rejected before the record is read.
pub const MAX_RECORD: usize = MAX_PLAINTEXT + OVERHEAD;
/// The first bytes of a HELLO: identifies an astream sealed transport, version 1.
pub const HELLO_MAGIC: [u8; 4] = *b"ASE\x01";
/// The random bytes in a HELLO (from the OS CSPRNG): the per-connection freshness
/// each side contributes.
pub const SESSION_NONCE_LEN: usize = 32;
/// On-wire length of one HELLO: `HELLO_MAGIC ‖ session nonce`.
pub const HELLO_LEN: usize = 4 + SESSION_NONCE_LEN;

const DIR_CLIENT_TO_SERVER: u8 = 0x01;
const DIR_SERVER_TO_CLIENT: u8 = 0x02;
const LEN_PREFIX: usize = 4;

/// A stream whose `try_clone` yields a second handle to the SAME underlying
/// connection (independent read/write directions on one fd). Implemented for the
/// std socket types; lets [`SealedStream`] mirror their duplex-by-clone model.
pub trait TryCloneable: Sized {
    /// A second handle to the same connection.
    ///
    /// # Errors
    /// Propagates the OS `dup`/`try_clone` failure.
    fn try_clone(&self) -> io::Result<Self>;
}

impl TryCloneable for std::net::TcpStream {
    fn try_clone(&self) -> io::Result<Self> {
        std::net::TcpStream::try_clone(self)
    }
}

#[cfg(unix)]
impl TryCloneable for std::os::unix::net::UnixStream {
    fn try_clone(&self) -> io::Result<Self> {
        std::os::unix::net::UnixStream::try_clone(self)
    }
}

/// The per-connection binding the handshake establishes: the AAD prefix for the
/// records this side sends and for the records it receives. The two differ only
/// in the direction byte.
///
/// The binding is whatever material the handshake above this record layer agreed
/// on, so one record layer serves both handshakes astream ships:
///
/// * the PSK-only wire ([`SealedStream::handshake_client`]) binds
///   `hello_client ‖ hello_server` — two 32-byte CSPRNG nonces exchanged in the
///   clear, which is all the freshness a bare pre-shared key can offer;
/// * the forward-secret and identity handshakes
///   ([`SealedStream::with_transcript`]) bind their own TRANSCRIPT — the ephemeral
///   X25519 public keys as each side saw them. That is strictly stronger and costs
///   no extra round trip: the transcript is already what the session key derives
///   from, and under the identity handshake it is what both peers SIGN, so a
///   record cannot be lifted into a session whose transcript differs.
#[derive(Clone)]
struct Session {
    send: Vec<u8>,
    recv: Vec<u8>,
}

impl Session {
    /// `binding ‖ direction`, one prefix per direction.
    fn from_binding(binding: &[u8], is_client: bool) -> Session {
        let (dir_send, dir_recv) = if is_client {
            (DIR_CLIENT_TO_SERVER, DIR_SERVER_TO_CLIENT)
        } else {
            (DIR_SERVER_TO_CLIENT, DIR_CLIENT_TO_SERVER)
        };
        let mut send = Vec::with_capacity(binding.len() + 1);
        send.extend_from_slice(binding);
        let mut recv = send.clone();
        send.push(dir_send);
        recv.push(dir_recv);
        Session { send, recv }
    }

    fn from_hellos(
        hello_client: &[u8; HELLO_LEN],
        hello_server: &[u8; HELLO_LEN],
        is_client: bool,
    ) -> Session {
        let mut binding = Vec::with_capacity(2 * HELLO_LEN);
        binding.extend_from_slice(hello_client);
        binding.extend_from_slice(hello_server);
        Session::from_binding(&binding, is_client)
    }
}

/// Set `aad` to the AAD of record `seq` in the direction `prefix` describes,
/// `prefix ‖ seq`, reusing its allocation.
fn record_aad(aad: &mut Vec<u8>, prefix: &[u8], seq: u64) {
    aad.clear();
    aad.extend_from_slice(prefix);
    aad.extend_from_slice(&seq.to_le_bytes());
}

/// The send half's mutable state.
struct SendState {
    /// The sequence the next record is sealed under.
    seq: u64,
    /// Set once a record was only partly written: the peer can no longer parse
    /// the wire past it, so every later write errors instead of sealing records
    /// the peer will never open.
    poisoned: bool,
    /// The record being written, `len ‖ nonce ‖ ciphertext ‖ tag`, and its AAD.
    /// Kept across records so a write allocates nothing once warm; `rec` holds
    /// at most `LEN_PREFIX + MAX_RECORD` bytes, and only ciphertext at rest.
    rec: Vec<u8>,
    aad: Vec<u8>,
}

impl SendState {
    fn new() -> SendState {
        SendState {
            seq: 0,
            poisoned: false,
            rec: Vec::new(),
            aad: Vec::new(),
        }
    }
}

/// The receive half's mutable state.
struct RecvState {
    /// The sequence the next record must carry.
    seq: u64,
    /// The record buffer. While a record is being read it holds the sealed bytes
    /// (`rec[..body_len]`, filled to `body_filled`); once opened in place, the
    /// plaintext is `rec[pos..end]` and `read` drains it. It only grows (to at
    /// most `MAX_RECORD`), so a record costs no allocation and no zero-fill.
    rec: Vec<u8>,
    pos: usize,
    end: usize,
    /// The AAD scratch for the record being opened.
    aad: Vec<u8>,
    /// The in-progress wire read — the 4-byte length prefix, then the body —
    /// accumulated across partial and timed-out transport reads so a socket
    /// timeout never desyncs the record boundary (the broker's liveness probe
    /// reads with a 50 ms timeout).
    hdr: [u8; LEN_PREFIX],
    hdr_filled: usize,
    /// The declared body length once the prefix is complete (0 = not yet).
    body_len: usize,
    body_filled: usize,
    /// Set once a record failed to authenticate (or a prefix was out of range):
    /// the stream is unusable from there on — every later `read` errors.
    poisoned: bool,
}

impl RecvState {
    fn new() -> RecvState {
        RecvState {
            seq: 0,
            rec: Vec::new(),
            pos: 0,
            end: 0,
            aad: Vec::new(),
            hdr: [0u8; LEN_PREFIX],
            hdr_filled: 0,
            body_len: 0,
            body_filled: 0,
            poisoned: false,
        }
    }
}

/// A transparent AEAD wrapper over a byte stream `S`. See the module docs.
pub struct SealedStream<S> {
    inner: S,
    key: [u8; KEY_LEN],
    session: Session,
    // The per-record AAD counters, SHARED across try_clone so two handles to one
    // socket write a single ordered record sequence and read against a single
    // expected sequence.
    send: Arc<Mutex<SendState>>,
    recv: Arc<Mutex<RecvState>>,
}

impl<S> SealedStream<S> {
    fn with_session(inner: S, key: [u8; KEY_LEN], session: Session) -> Self {
        SealedStream {
            inner,
            key,
            session,
            send: Arc::new(Mutex::new(SendState::new())),
            recv: Arc::new(Mutex::new(RecvState::new())),
        }
    }

    /// The underlying stream, for transport-level control (timeouts, shutdown)
    /// that does not touch the record bytes.
    pub fn get_ref(&self) -> &S {
        &self.inner
    }
}

impl<S: Read + Write> SealedStream<S> {
    /// Wrap a stream whose key and TRANSCRIPT a handshake above this layer already
    /// established — the forward-secret (`client_handshake`, `handshake` feature) and identity
    /// (`client_identity_handshake`, `identity` feature) paths.
    ///
    /// No hello exchange and no confirm record: those exist to give a bare
    /// pre-shared key freshness and key confirmation, and a key agreement has
    /// already provided both. `transcript` is bound into every record's AAD
    /// (`transcript ‖ direction ‖ seq`), so a record is valid only for this
    /// session, this direction and this position — and because the transcript is
    /// what the session key derives from (and, under the identity handshake, what
    /// both peers sign), a record cannot be lifted into any other session.
    ///
    /// `is_client` must be the side's real role: it picks the direction byte, and
    /// two peers that disagree cannot open each other's records.
    pub fn with_transcript(
        inner: S,
        key: [u8; KEY_LEN],
        transcript: &[u8],
        is_client: bool,
    ) -> Self {
        Self::with_session(inner, key, Session::from_binding(transcript, is_client))
    }

    /// Open the client end of a sealed stream over `inner` under the pre-shared
    /// `key`: run the handshake (see the module docs) against a peer that runs
    /// [`handshake_server`](Self::handshake_server). Returns only after the
    /// peer's confirm record has opened — i.e. the peer has proven it holds the
    /// key and saw the same two hellos.
    ///
    /// # Errors
    /// The transport error; `InvalidData` if the peer is not an astream sealed
    /// transport or its confirm fails to authenticate (wrong key, tampered
    /// hello); `UnexpectedEof` if the peer closed mid-handshake.
    pub fn handshake_client(inner: S, key: [u8; KEY_LEN]) -> io::Result<Self> {
        Self::handshake(inner, key, true)
    }

    /// Open the server end of a sealed stream over `inner` under the pre-shared
    /// `key`, against a peer running [`handshake_client`](Self::handshake_client).
    /// Before the peer has authenticated this reads exactly one hello and one
    /// empty confirm record — nothing larger can be forced.
    ///
    /// # Errors
    /// As [`handshake_client`](Self::handshake_client).
    pub fn handshake_server(inner: S, key: [u8; KEY_LEN]) -> io::Result<Self> {
        Self::handshake(inner, key, false)
    }

    fn handshake(mut inner: S, key: [u8; KEY_LEN], is_client: bool) -> io::Result<Self> {
        // 1. HELLO, in the clear: magic ‖ fresh CSPRNG bytes. Both sides send
        //    first and read second — a hello never fills a socket buffer, so there
        //    is no deadlock.
        let mut mine = [0u8; HELLO_LEN];
        mine[..HELLO_MAGIC.len()].copy_from_slice(&HELLO_MAGIC);
        getrandom::getrandom(&mut mine[HELLO_MAGIC.len()..])
            .map_err(|e| io::Error::other(e.to_string()))?;
        inner.write_all(&mine)?;
        inner.flush()?;
        let mut theirs = [0u8; HELLO_LEN];
        inner.read_exact(&mut theirs)?;
        if theirs[..HELLO_MAGIC.len()] != HELLO_MAGIC {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "peer is not an astream sealed transport (bad hello)",
            ));
        }
        let (hello_client, hello_server) = if is_client {
            (mine, theirs)
        } else {
            (theirs, mine)
        };
        let mut stream = Self::with_session(
            inner,
            key,
            Session::from_hellos(&hello_client, &hello_server, is_client),
        );

        // 2. CONFIRM: record 0 of each direction, empty. Sealing it proves
        //    possession of the key and binds BOTH hellos (they are its AAD);
        //    opening the peer's proves the same of the peer. Again send first,
        //    read second.
        {
            let mut tx = stream.send.lock().unwrap();
            write_record(
                &mut stream.inner,
                &stream.key,
                &stream.session,
                &mut tx,
                b"",
            )?;
        }
        stream.inner.flush()?;
        {
            let mut rs = stream.recv.lock().unwrap();
            // The confirm is empty, so the one pre-authentication record read is
            // capped at exactly one empty record: an unkeyed peer cannot make us
            // allocate anything larger.
            let got = read_record(
                &mut stream.inner,
                &stream.key,
                &stream.session,
                &mut rs,
                OVERHEAD,
            )
            .map_err(|e| {
                if e.kind() == io::ErrorKind::InvalidData {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        "sealed handshake failed to authenticate (wrong key or tampered hello)",
                    )
                } else {
                    e
                }
            })?;
            if !got {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "peer closed during the sealed handshake",
                ));
            }
            if rs.pos != rs.end {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "malformed sealed handshake confirm",
                ));
            }
        }
        Ok(stream)
    }
}

impl<S: TryCloneable> SealedStream<S> {
    /// A second handle to the same connection, SHARING the AEAD record counters
    /// (and the session binding).
    ///
    /// # Errors
    /// Propagates the underlying `try_clone` failure.
    pub fn try_clone(&self) -> io::Result<Self> {
        Ok(SealedStream {
            inner: self.inner.try_clone()?,
            key: self.key,
            session: self.session.clone(),
            send: Arc::clone(&self.send),
            recv: Arc::clone(&self.recv),
        })
    }
}

/// Seal `plaintext` (at most `MAX_PLAINTEXT` bytes) as record `tx.seq` of this
/// side's direction and write it: `len ‖ nonce ‖ ciphertext ‖ tag`, sealed in
/// place in `tx.rec`. Advances `tx.seq` once the bytes are written.
///
/// An error before any byte of the record reached the transport leaves the
/// stream intact: a retry seals the record afresh under the same sequence. An
/// error after some did poisons the send side, because the peer's record
/// boundary is then lost for good.
fn write_record<S: Write>(
    inner: &mut S,
    key: &[u8; KEY_LEN],
    session: &Session,
    tx: &mut SendState,
    plaintext: &[u8],
) -> io::Result<()> {
    debug_assert!(plaintext.len() <= MAX_PLAINTEXT);
    if tx.poisoned {
        return Err(io::Error::other(
            "sealed stream: an earlier record was only partly written",
        ));
    }
    let sealed_len = NONCE_LEN + plaintext.len() + TAG_LEN;
    let mut nonce = [0u8; NONCE_LEN];
    getrandom::getrandom(&mut nonce).map_err(|e| io::Error::other(e.to_string()))?;
    tx.rec.clear();
    tx.rec.reserve(LEN_PREFIX + sealed_len);
    tx.rec.extend_from_slice(&(sealed_len as u32).to_le_bytes());
    tx.rec.extend_from_slice(&nonce);
    tx.rec.extend_from_slice(plaintext);
    record_aad(&mut tx.aad, &session.send, tx.seq);
    seal_in_place(key, &tx.aad, &mut tx.rec, LEN_PREFIX);
    let mut sent = 0;
    while sent < tx.rec.len() {
        let err = match inner.write(&tx.rec[sent..]) {
            Ok(0) => io::Error::from(io::ErrorKind::WriteZero),
            Ok(k) => {
                sent += k;
                continue;
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => e,
        };
        tx.poisoned = sent > 0;
        return Err(err);
    }
    tx.seq = tx.seq.wrapping_add(1);
    Ok(())
}

/// Read `buf[*filled..]` to the end, resuming from `*filled`. A transport error
/// (a timeout included) leaves `*filled` at the resumable position; an EOF
/// before the end is truncation (`UnexpectedEof`).
fn fill<S: Read>(inner: &mut S, buf: &mut [u8], filled: &mut usize) -> io::Result<()> {
    while *filled < buf.len() {
        match inner.read(&mut buf[*filled..]) {
            Ok(0) => {
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "sealed record truncated",
                ))
            }
            Ok(k) => *filled += k,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    Ok(())
}

/// Read and open the next record (of at most `limit` sealed bytes) into `rs`.
/// `Ok(false)` is a clean EOF at a record boundary — an orderly close. A
/// timeout / `WouldBlock` from the transport returns that error with the partial
/// read kept in `rs`, to be resumed by the next call.
fn read_record<S: Read>(
    inner: &mut S,
    key: &[u8; KEY_LEN],
    session: &Session,
    rs: &mut RecvState,
    limit: usize,
) -> io::Result<bool> {
    if rs.poisoned {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "sealed stream failed to authenticate earlier",
        ));
    }
    if rs.body_len == 0 {
        if rs.hdr_filled == 0 {
            // At a record boundary a clean EOF is an orderly close.
            let n = loop {
                match inner.read(&mut rs.hdr) {
                    Ok(n) => break n,
                    Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                    Err(e) => return Err(e),
                }
            };
            if n == 0 {
                return Ok(false);
            }
            rs.hdr_filled = n;
        }
        fill(inner, &mut rs.hdr, &mut rs.hdr_filled)?;
        let n = u32::from_le_bytes(rs.hdr) as usize;
        if !(OVERHEAD..=limit).contains(&n) {
            rs.poisoned = true;
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "sealed record length out of range",
            ));
        }
        rs.body_len = n;
        rs.body_filled = 0;
        if rs.rec.len() < n {
            rs.rec.resize(n, 0);
        }
    }
    let n = rs.body_len;
    fill(inner, &mut rs.rec[..n], &mut rs.body_filled)?;
    record_aad(&mut rs.aad, &session.recv, rs.seq);
    let end = match open_in_place(key, &rs.aad, &mut rs.rec[..n]) {
        Ok(plain) => NONCE_LEN + plain.len(),
        Err(_) => {
            rs.poisoned = true;
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "sealed record failed to authenticate",
            ));
        }
    };
    rs.seq = rs.seq.wrapping_add(1);
    rs.pos = NONCE_LEN;
    rs.end = end;
    rs.hdr_filled = 0;
    rs.body_len = 0;
    rs.body_filled = 0;
    Ok(true)
}

impl<S: Write> Write for SealedStream<S> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if buf.is_empty() {
            // Nothing to seal; an empty write puts no record on the wire.
            return Ok(0);
        }
        // One write ⇒ one or more records, all under the send lock, so records
        // from two handles never interleave within a write and each record's
        // sequence matches its position on the wire.
        let mut tx = self.send.lock().unwrap();
        let mut written = 0;
        for chunk in buf.chunks(MAX_PLAINTEXT) {
            if let Err(e) = write_record(&mut self.inner, &self.key, &self.session, &mut tx, chunk)
            {
                // Records already on the wire are bytes this call consumed and
                // must be reported as such: an `Err` tells the caller nothing was
                // written, and a retry would re-send them as fresh, valid records
                // the peer accepts twice. A persistent error resurfaces on the
                // next call (a record cut part-way poisons the send side).
                return if written == 0 { Err(e) } else { Ok(written) };
            }
            written += chunk.len();
        }
        Ok(written)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

impl<S: Read> Read for SealedStream<S> {
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        if out.is_empty() {
            return Ok(0);
        }
        let mut rs = self.recv.lock().unwrap();
        while rs.pos >= rs.end {
            // Drained (or nothing open yet): read and open the next record. An
            // empty record — the handshake confirm, or a peer's empty write — is
            // skipped here; `Ok(0)` is reserved for EOF at a record boundary.
            if !read_record(
                &mut self.inner,
                &self.key,
                &self.session,
                &mut rs,
                MAX_RECORD,
            )? {
                return Ok(0);
            }
        }
        let k = (rs.end - rs.pos).min(out.len());
        let pos = rs.pos;
        out[..k].copy_from_slice(&rs.rec[pos..pos + k]);
        rs.pos += k;
        Ok(k)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;
    use std::net::{TcpListener, TcpStream};
    use std::time::Duration;

    const KEY: [u8; KEY_LEN] = [7u8; KEY_LEN];

    fn hello(fill: u8) -> [u8; HELLO_LEN] {
        let mut h = [fill; HELLO_LEN];
        h[..4].copy_from_slice(&HELLO_MAGIC);
        h
    }

    /// A fixed (client, server) session pair, for in-memory tests that need no
    /// socket: the client side seals c→s, the server side opens c→s.
    fn sessions() -> (Session, Session) {
        let (hc, hs) = (hello(0xc1), hello(0x5e));
        (
            Session::from_hellos(&hc, &hs, true),
            Session::from_hellos(&hc, &hs, false),
        )
    }

    /// Split a wire (a sequence of `len ‖ sealed` records) into its records.
    fn records(wire: &[u8]) -> Vec<&[u8]> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < wire.len() {
            let n = u32::from_le_bytes([wire[i], wire[i + 1], wire[i + 2], wire[i + 3]]) as usize;
            out.push(&wire[i..i + 4 + n]);
            i += 4 + n;
        }
        out
    }

    fn read_all<R: Read>(r: &mut R, chunk: usize) -> Vec<u8> {
        let mut got = Vec::new();
        let mut buf = vec![0u8; chunk];
        loop {
            let n = r.read(&mut buf).unwrap();
            if n == 0 {
                break;
            }
            got.extend_from_slice(&buf[..n]);
        }
        got
    }

    /// After a record has failed, the stream is poisoned: every later read errors
    /// too (never `Ok(0)`, never bytes) — nothing past an unauthentic record is
    /// ever yielded.
    fn assert_poisoned<S: Read>(r: &mut SealedStream<S>) {
        let mut buf = [0u8; 8];
        assert!(
            r.read(&mut buf).is_err(),
            "a poisoned stream must keep erroring"
        );
        assert!(
            r.read(&mut buf).is_err(),
            "a poisoned stream must keep erroring"
        );
    }

    // ---- the record layer, in memory ------------------------------------------

    #[test]
    fn frames_round_trip_through_the_record_layer() {
        let (sc, ss) = sessions();
        let mut w = SealedStream::with_session(Vec::<u8>::new(), KEY, sc.clone());
        // Three independent writes ⇒ three records on the wire.
        w.write_all(b"hello ").unwrap();
        w.write_all(b"sealed ").unwrap();
        w.write_all(b"world").unwrap();
        let wire = w.get_ref().clone();
        assert_eq!(records(&wire).len(), 3);

        // The wire is NOT plaintext.
        assert!(!wire.windows(5).any(|c| c == b"hello"));

        // A reader reassembles the byte stream across record boundaries — a read
        // buffer smaller than a record still drains correctly.
        let mut r = SealedStream::with_session(Cursor::new(wire), KEY, ss.clone());
        assert_eq!(read_all(&mut r, 4), b"hello sealed world");
    }

    #[test]
    fn a_flipped_record_byte_fails_to_open() {
        let (sc, ss) = sessions();
        let mut w = SealedStream::with_session(Vec::<u8>::new(), KEY, sc.clone());
        w.write_all(b"integrity").unwrap();
        let mut wire = w.get_ref().clone();
        let last = wire.len() - 1;
        wire[last] ^= 0x01; // corrupt the tag
        let mut r = SealedStream::with_session(Cursor::new(wire), KEY, ss.clone());
        let mut buf = [0u8; 32];
        let e = r.read(&mut buf).unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::InvalidData);
        // Poisoned from here on: the stream never yields bytes again.
        assert_poisoned(&mut r);
    }

    #[test]
    fn a_reordered_record_fails_to_open() {
        // Two records; swap them on the wire. The second (now first) opens under
        // sequence 0, but was sealed under sequence 1 ⇒ AAD mismatch ⇒ error.
        let (sc, ss) = sessions();
        let mut w = SealedStream::with_session(Vec::<u8>::new(), KEY, sc.clone());
        w.write_all(b"first__").unwrap();
        w.write_all(b"second_").unwrap();
        let wire = w.get_ref().clone();
        let recs = records(&wire);
        let swapped = [recs[1], recs[0]].concat();
        let mut r = SealedStream::with_session(Cursor::new(swapped), KEY, ss.clone());
        let mut buf = [0u8; 32];
        assert!(r.read(&mut buf).is_err());
        assert_poisoned(&mut r);
    }

    #[test]
    fn a_replayed_or_dropped_record_fails_to_open() {
        let (sc, ss) = sessions();
        let mut w = SealedStream::with_session(Vec::<u8>::new(), KEY, sc.clone());
        w.write_all(b"one").unwrap();
        w.write_all(b"two").unwrap();
        let wire = w.get_ref().clone();
        let recs = records(&wire);

        // Replay: record 0 twice. The first copy opens; the second is sealed
        // under sequence 0 but arrives at sequence 1 ⇒ rejected.
        let replayed = [recs[0], recs[0]].concat();
        let mut r = SealedStream::with_session(Cursor::new(replayed), KEY, ss.clone());
        let mut buf = [0u8; 3];
        r.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"one");
        assert!(r.read(&mut buf).is_err());
        assert_poisoned(&mut r);

        // Drop: record 1 alone arrives at sequence 0 ⇒ rejected.
        let mut r = SealedStream::with_session(Cursor::new(recs[1].to_vec()), KEY, ss.clone());
        assert!(r.read(&mut buf).is_err());
        assert_poisoned(&mut r);
    }

    #[test]
    fn the_wrong_key_fails_to_open() {
        let (sc, ss) = sessions();
        let mut w = SealedStream::with_session(Vec::<u8>::new(), KEY, sc.clone());
        w.write_all(b"secret").unwrap();
        let wire = w.get_ref().clone();
        let mut r = SealedStream::with_session(Cursor::new(wire), [8u8; KEY_LEN], ss);
        let mut buf = [0u8; 32];
        assert!(r.read(&mut buf).is_err());
        assert_poisoned(&mut r);
    }

    #[test]
    fn a_record_for_the_other_direction_or_session_fails_to_open() {
        // The same bytes, sealed by the client for c→s, do not open as s→c
        // (reflection) nor under a session with a different hello (replay across
        // connections) — even at the same sequence and under the same key.
        let (sc, ss) = sessions();
        let mut w = SealedStream::with_session(Vec::<u8>::new(), KEY, sc.clone());
        w.write_all(b"bound").unwrap();
        let wire = w.get_ref().clone();
        let mut buf = [0u8; 32];

        // Reflected: read it back as the CLIENT (expects s→c).
        let mut r = SealedStream::with_session(Cursor::new(wire.clone()), KEY, sc.clone());
        assert!(r.read(&mut buf).is_err());
        assert_poisoned(&mut r);

        // Another connection: the server hello differs by one byte.
        let other = Session::from_hellos(&hello(0xc1), &hello(0x5f), false);
        let mut r = SealedStream::with_session(Cursor::new(wire.clone()), KEY, other);
        assert!(r.read(&mut buf).is_err());
        assert_poisoned(&mut r);

        // Control: the right session and direction opens it.
        let mut r = SealedStream::with_session(Cursor::new(wire), KEY, ss.clone());
        assert_eq!(read_all(&mut r, 32), b"bound");
    }

    #[test]
    fn a_max_size_frame_spans_bounded_records_and_round_trips() {
        // The broker's largest frame is HEADER_SIZE (12) + MAX_PAYLOAD_LEN (16 MiB).
        // One write of it is split into ceil(len / MAX_PLAINTEXT) records, every
        // one within MAX_RECORD on the wire, and reassembles byte-for-byte.
        let len: usize = 16 * 1024 * 1024 + 12;
        let frame: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
        let (sc, ss) = sessions();
        let mut w = SealedStream::with_session(Vec::<u8>::new(), KEY, sc.clone());
        w.write_all(&frame).unwrap();
        let wire = w.get_ref().clone();
        let recs = records(&wire);
        assert_eq!(recs.len(), len.div_ceil(MAX_PLAINTEXT));
        assert!(recs.iter().all(|r| r.len() - 4 <= MAX_RECORD));
        assert_eq!(recs[0].len() - 4, MAX_RECORD, "full records are MAX_RECORD");
        assert_eq!(wire.len(), len + recs.len() * (4 + OVERHEAD));

        let mut r = SealedStream::with_session(Cursor::new(wire), KEY, ss.clone());
        assert_eq!(read_all(&mut r, 1 << 20), frame);
    }

    #[test]
    fn an_oversized_length_prefix_is_rejected_before_the_body_is_read() {
        // A prefix above MAX_RECORD: rejected on the prefix alone. Only the four
        // prefix bytes exist on this wire, so any attempt to read the body would
        // surface as UnexpectedEof instead of InvalidData.
        let (_, ss) = sessions();
        let wire = ((MAX_RECORD + 1) as u32).to_le_bytes().to_vec();
        let mut r = SealedStream::with_session(Cursor::new(wire), KEY, ss.clone());
        let mut buf = [0u8; 8];
        let e = r.read(&mut buf).unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::InvalidData);
        // And a prefix below OVERHEAD (no room for nonce + tag) likewise.
        let wire = ((OVERHEAD - 1) as u32).to_le_bytes().to_vec();
        let mut r = SealedStream::with_session(Cursor::new(wire), KEY, ss.clone());
        let e = r.read(&mut buf).unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn an_empty_record_is_skipped_not_reported_as_eof() {
        // An empty write puts nothing on the wire...
        let (sc, ss) = sessions();
        let mut w = SealedStream::with_session(Vec::<u8>::new(), KEY, sc.clone());
        assert_eq!(w.write(b"").unwrap(), 0);
        assert!(w.get_ref().is_empty());
        // ...and an empty RECORD from the peer (sealed directly, as the handshake
        // confirm is) is skipped: `read` moves on to the next record instead of
        // returning Ok(0), which every std consumer would take as end-of-stream.
        w.write_all(b"ab").unwrap();
        {
            let mut tx = w.send.lock().unwrap();
            write_record(&mut w.inner, &w.key, &w.session, &mut tx, b"").unwrap();
        }
        w.write_all(b"cd").unwrap();
        let wire = w.get_ref().clone();
        assert_eq!(records(&wire).len(), 3);
        let mut r = SealedStream::with_session(Cursor::new(wire), KEY, ss.clone());
        let mut buf = [0u8; 2];
        r.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"ab");
        r.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"cd");
        assert_eq!(r.read(&mut buf).unwrap(), 0, "true EOF at the boundary");
    }

    /// A transport that hands out at most one byte per read and reports a
    /// timeout on every other call — the shape of a socket with a read timeout.
    struct Choppy {
        data: Vec<u8>,
        at: usize,
        calls: usize,
    }
    impl Read for Choppy {
        fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
            self.calls += 1;
            if self.calls.is_multiple_of(2) {
                return Err(io::Error::new(io::ErrorKind::TimedOut, "probe"));
            }
            if self.at >= self.data.len() || out.is_empty() {
                return Ok(0);
            }
            out[0] = self.data[self.at];
            self.at += 1;
            Ok(1)
        }
    }

    #[test]
    fn a_timed_out_transport_read_resumes_at_the_same_record_boundary() {
        let (sc, ss) = sessions();
        let mut w = SealedStream::with_session(Vec::<u8>::new(), KEY, sc.clone());
        w.write_all(b"survive ").unwrap();
        w.write_all(b"timeouts").unwrap();
        let wire = w.get_ref().clone();
        let choppy = Choppy {
            data: wire,
            at: 0,
            calls: 0,
        };
        let mut r = SealedStream::with_session(choppy, KEY, ss.clone());
        let mut got = Vec::new();
        let mut buf = [0u8; 5];
        let mut timeouts = 0;
        loop {
            match r.read(&mut buf) {
                Ok(0) => break,
                Ok(n) => got.extend_from_slice(&buf[..n]),
                Err(e) if e.kind() == io::ErrorKind::TimedOut => timeouts += 1,
                Err(e) => panic!("unexpected {e}"),
            }
        }
        assert_eq!(got, b"survive timeouts");
        assert!(timeouts > 0, "the transport did time out mid-record");
    }

    /// A transport that times out ONCE when `stall_at` bytes have been accepted:
    /// a write that would cross that offset takes only the bytes up to it (a
    /// short write), and the next call fails with `TimedOut` having taken none —
    /// the shape of a socket with `SO_SNDTIMEO` whose peer stopped reading.
    struct Stall {
        wire: Vec<u8>,
        stall_at: usize,
        fired: bool,
    }
    impl Stall {
        fn new(stall_at: usize) -> Stall {
            Stall {
                wire: Vec::new(),
                stall_at,
                fired: false,
            }
        }
    }
    impl Write for Stall {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            let mut take = buf.len();
            if !self.fired {
                if self.wire.len() == self.stall_at {
                    self.fired = true;
                    return Err(io::Error::new(io::ErrorKind::TimedOut, "stalled"));
                }
                take = take.min(self.stall_at - self.wire.len());
            }
            self.wire.extend_from_slice(&buf[..take]);
            Ok(take)
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn a_write_that_stalls_after_whole_records_reports_them_written() {
        // The first record goes out whole and the transport stalls exactly at the
        // boundary before the second. `write` must report the first record's bytes
        // as written (`Ok(n)`), as the `Write` contract requires: an `Err` tells
        // the caller that NOTHING was written, and a caller that then retries the
        // same buffer re-sends bytes the peer already has, as fresh, valid records.
        let (sc, ss) = sessions();
        let data: Vec<u8> = (0..2 * MAX_PLAINTEXT + 10)
            .map(|i| (i % 251) as u8)
            .collect();
        let first_record = LEN_PREFIX + MAX_PLAINTEXT + OVERHEAD;
        let mut w = SealedStream::with_session(Stall::new(first_record), KEY, sc);

        // A caller that treats the timeout as transient and retries what `write`
        // did not report written.
        let mut off = 0;
        while off < data.len() {
            match w.write(&data[off..]) {
                Ok(n) => off += n,
                Err(e) if e.kind() == io::ErrorKind::TimedOut => {}
                Err(e) => panic!("unexpected {e}"),
            }
        }
        assert!(w.inner.fired, "the transport did stall");
        let mut r = SealedStream::with_session(Cursor::new(w.inner.wire), KEY, ss);
        let got = read_all(&mut r, 1 << 16);
        assert_eq!(got.len(), data.len(), "each byte arrives exactly once");
        assert!(got == data);
    }

    #[test]
    fn a_record_cut_part_way_poisons_the_send_side() {
        // The transport takes 10 bytes of the first record, then times out. That
        // record can never be completed, so the peer cannot parse anything after
        // it: every later write must fail rather than report success for records
        // appended to a wire the peer will reject.
        let (sc, _) = sessions();
        let mut w = SealedStream::with_session(Stall::new(10), KEY, sc);
        let e = w.write(b"first").unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::TimedOut);
        assert!(
            w.write(b"second").is_err(),
            "a cut record poisons the stream"
        );
        assert!(w.write(b"third").is_err(), "and it stays poisoned");
        assert_eq!(w.inner.wire.len(), 10, "nothing is sealed after the cut");
    }

    #[test]
    fn a_write_that_stalls_before_its_record_starts_can_be_retried() {
        // Nothing of the record reached the transport, so the stream is intact:
        // the retry seals it again under the same sequence and the peer reads it.
        let (sc, ss) = sessions();
        let mut w = SealedStream::with_session(Stall::new(0), KEY, sc);
        let e = w.write(b"retry me").unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::TimedOut);
        assert!(w.inner.wire.is_empty());
        w.write_all(b"retry me").unwrap();
        let mut r = SealedStream::with_session(Cursor::new(w.inner.wire), KEY, ss);
        assert_eq!(read_all(&mut r, 64), b"retry me");
    }

    // ---- the handshake, over real sockets --------------------------------------

    /// Records every byte written through it and every byte read through it (the
    /// client's view of both directions of the wire).
    struct Tap<S> {
        inner: S,
        sent: Arc<Mutex<Vec<u8>>>,
        received: Arc<Mutex<Vec<u8>>>,
    }
    impl<S: Read> Read for Tap<S> {
        fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
            let n = self.inner.read(out)?;
            self.received.lock().unwrap().extend_from_slice(&out[..n]);
            Ok(n)
        }
    }
    impl<S: Write> Write for Tap<S> {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            let n = self.inner.write(buf)?;
            self.sent.lock().unwrap().extend_from_slice(&buf[..n]);
            Ok(n)
        }
        fn flush(&mut self) -> io::Result<()> {
            self.inner.flush()
        }
    }
    impl<S: TryCloneable> TryCloneable for Tap<S> {
        fn try_clone(&self) -> io::Result<Self> {
            Ok(Tap {
                inner: self.inner.try_clone()?,
                sent: Arc::clone(&self.sent),
                received: Arc::clone(&self.received),
            })
        }
    }

    fn tcp_pair() -> (TcpStream, TcpStream) {
        let l = TcpListener::bind("127.0.0.1:0").unwrap();
        let addr = l.local_addr().unwrap();
        let c = TcpStream::connect(addr).unwrap();
        let (s, _) = l.accept().unwrap();
        for x in [&c, &s] {
            x.set_read_timeout(Some(Duration::from_secs(5))).unwrap();
        }
        (c, s)
    }

    struct Conn {
        client: io::Result<SealedStream<Tap<TcpStream>>>,
        server: io::Result<SealedStream<TcpStream>>,
        /// Raw handles to the same two sockets, for injecting bytes underneath
        /// the record layer.
        raw_client: TcpStream,
        raw_server: TcpStream,
        /// Everything the client end wrote, in order.
        sent: Arc<Mutex<Vec<u8>>>,
        /// Everything the client end read (the server's bytes), in order.
        received: Arc<Mutex<Vec<u8>>>,
    }

    fn connect(key_client: [u8; KEY_LEN], key_server: [u8; KEY_LEN]) -> Conn {
        let (c, s) = tcp_pair();
        let raw_client = c.try_clone().unwrap();
        let raw_server = s.try_clone().unwrap();
        let sent = Arc::new(Mutex::new(Vec::new()));
        let received = Arc::new(Mutex::new(Vec::new()));
        let tap = Tap {
            inner: c,
            sent: Arc::clone(&sent),
            received: Arc::clone(&received),
        };
        let t = std::thread::spawn(move || SealedStream::handshake_client(tap, key_client));
        let server = SealedStream::handshake_server(s, key_server);
        let client = t.join().unwrap();
        Conn {
            client,
            server,
            raw_client,
            raw_server,
            sent,
            received,
        }
    }

    /// The client's next record on the wire after `mark` bytes were sent.
    fn last_record(sent: &Arc<Mutex<Vec<u8>>>, mark: usize) -> Vec<u8> {
        sent.lock().unwrap()[mark..].to_vec()
    }

    #[test]
    fn the_handshake_exchanges_fresh_hellos_and_confirms_the_key() {
        let a = connect(KEY, KEY);
        let b = connect(KEY, KEY);
        let (mut ca, mut sa) = (a.client.unwrap(), a.server.unwrap());
        let _ = (b.client.unwrap(), b.server.unwrap());
        // The client sent its hello (magic ‖ nonce) and then its confirm record.
        let (sent_a, sent_b) = (
            a.sent.lock().unwrap().clone(),
            b.sent.lock().unwrap().clone(),
        );
        assert_eq!(sent_a.len(), HELLO_LEN + 4 + OVERHEAD);
        assert_eq!(&sent_a[..4], &HELLO_MAGIC);
        assert_ne!(sent_a[..HELLO_LEN], sent_b[..HELLO_LEN], "hellos are fresh");
        // Application bytes flow both ways after it.
        ca.write_all(b"ping").unwrap();
        let mut buf = [0u8; 4];
        sa.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"ping");
        sa.write_all(b"pong").unwrap();
        ca.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"pong");
    }

    #[test]
    fn every_record_aad_is_hello_client_hello_server_direction_seq() {
        // Pins the binding ITSELF, not only its consequences: records captured off
        // the wire open with the raw primitive under a hand-built AAD of exactly
        // hello_client ‖ hello_server ‖ direction ‖ seq (u64 LE) — 0x01 for
        // client→server, 0x02 for server→client, seq from 0 with the confirm as
        // record 0 — and under no other direction, sequence, or hello order. Any
        // change to the layout (or to what it binds) fails here.
        let a = connect(KEY, KEY);
        let (mut ca, mut sa) = (a.client.unwrap(), a.server.unwrap());
        ca.write_all(b"pin the aad").unwrap();
        let mut buf = [0u8; 11];
        sa.read_exact(&mut buf).unwrap();
        sa.write_all(b"and back").unwrap();
        let mut back = [0u8; 8];
        ca.read_exact(&mut back).unwrap();
        let sent = a.sent.lock().unwrap().clone();
        let received = a.received.lock().unwrap().clone();

        // The hellos are the first HELLO_LEN bytes each way, in the clear.
        let hello_c: [u8; HELLO_LEN] = sent[..HELLO_LEN].try_into().unwrap();
        let hello_s: [u8; HELLO_LEN] = received[..HELLO_LEN].try_into().unwrap();
        assert_eq!(&hello_c[..4], &HELLO_MAGIC);
        assert_eq!(&hello_s[..4], &HELLO_MAGIC);
        let aad = |dir: u8, seq: u64| -> Vec<u8> {
            let mut v = Vec::with_capacity(2 * HELLO_LEN + 1 + 8);
            v.extend_from_slice(&hello_c);
            v.extend_from_slice(&hello_s);
            v.push(dir);
            v.extend_from_slice(&seq.to_le_bytes());
            v
        };

        // Client→server: the empty confirm is record 0, "pin the aad" is record 1.
        let c_recs = records(&sent[HELLO_LEN..]);
        assert_eq!(c_recs.len(), 2);
        assert_eq!(
            crate::open(&KEY, &aad(0x01, 0), &c_recs[0][4..]).unwrap(),
            b""
        );
        assert_eq!(
            crate::open(&KEY, &aad(0x01, 1), &c_recs[1][4..]).unwrap(),
            b"pin the aad"
        );
        // Server→client: likewise, under direction 0x02.
        let s_recs = records(&received[HELLO_LEN..]);
        assert_eq!(s_recs.len(), 2);
        assert_eq!(
            crate::open(&KEY, &aad(0x02, 0), &s_recs[0][4..]).unwrap(),
            b""
        );
        assert_eq!(
            crate::open(&KEY, &aad(0x02, 1), &s_recs[1][4..]).unwrap(),
            b"and back"
        );

        // The same bytes under the other direction, another sequence, or the
        // hellos in the other order do not open: each field is load-bearing.
        let rec = &c_recs[1][4..];
        assert!(crate::open(&KEY, &aad(0x02, 1), rec).is_err(), "direction");
        assert!(crate::open(&KEY, &aad(0x01, 0), rec).is_err(), "sequence");
        assert!(crate::open(&KEY, &aad(0x01, 2), rec).is_err(), "sequence");
        let mut swapped = aad(0x01, 1);
        swapped[..2 * HELLO_LEN].rotate_left(HELLO_LEN);
        assert!(crate::open(&KEY, &swapped, rec).is_err(), "hello order");
    }

    #[test]
    fn a_record_from_another_connection_fails_to_open() {
        // Same key, same direction, same sequence — the only difference is the
        // connection (its two hellos). Connection A's first application record,
        // injected into connection B, must not open at B's server.
        let a = connect(KEY, KEY);
        let b = connect(KEY, KEY);
        let sent_a = Arc::clone(&a.sent);
        let (mut ca, mut sa) = (a.client.unwrap(), a.server.unwrap());
        let (_cb, mut sb) = (b.client.unwrap(), b.server.unwrap());
        let mark = sent_a.lock().unwrap().len();
        ca.write_all(b"ack for A").unwrap();
        let rec = last_record(&sent_a, mark);
        let mut buf = [0u8; 9];
        sa.read_exact(&mut buf).unwrap(); // valid on A...
        assert_eq!(&buf, b"ack for A");
        (&b.raw_client).write_all(&rec).unwrap(); // ...replayed into B
        let e = sb.read(&mut buf).unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn a_reflected_record_fails_to_open() {
        // A client→server record written back to the client (same connection,
        // same key, and — after the confirms — the same sequence number) must
        // not open: the direction byte is in the AAD.
        let a = connect(KEY, KEY);
        let sent_a = Arc::clone(&a.sent);
        let (mut ca, mut sa) = (a.client.unwrap(), a.server.unwrap());
        let mark = sent_a.lock().unwrap().len();
        ca.write_all(b"reflect me").unwrap();
        let rec = last_record(&sent_a, mark);
        let mut buf = [0u8; 10];
        sa.read_exact(&mut buf).unwrap();
        (&a.raw_server).write_all(&rec).unwrap();
        let e = ca.read(&mut buf).unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn the_wrong_key_is_refused_inside_the_handshake() {
        let mut other = KEY;
        other[0] ^= 0xff;
        let c = connect(KEY, other);
        let e = c.server.err().expect("server must refuse");
        assert_eq!(e.kind(), io::ErrorKind::InvalidData);
        let e = c.client.err().expect("client must refuse");
        assert_eq!(e.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn an_unkeyed_peer_is_refused_and_can_force_no_allocation() {
        // A raw peer with no key: a well-formed hello, then a "confirm" whose
        // length prefix declares more than an empty record. The server rejects
        // it on the prefix — before reading a body — so the peer's declared
        // length never becomes an allocation. Only the prefix is sent: if the
        // server tried to read the body it would hit the socket timeout, not
        // InvalidData.
        let (c, s) = tcp_pair();
        let t = std::thread::spawn(move || SealedStream::handshake_server(s, KEY));
        let mut raw = c;
        raw.write_all(&hello(0x11)).unwrap();
        let mut theirs = [0u8; HELLO_LEN];
        raw.read_exact(&mut theirs).unwrap();
        assert_eq!(&theirs[..4], &HELLO_MAGIC);
        raw.write_all(&((OVERHEAD + 1) as u32).to_le_bytes())
            .unwrap();
        let e = t.join().unwrap().err().expect("must refuse");
        assert_eq!(e.kind(), io::ErrorKind::InvalidData);

        // And a bad hello (not this transport at all) is refused at once.
        let (c, s) = tcp_pair();
        let t = std::thread::spawn(move || SealedStream::handshake_server(s, KEY));
        let mut raw = c;
        raw.write_all(&[0u8; HELLO_LEN]).unwrap();
        let e = t.join().unwrap().err().expect("must refuse");
        assert_eq!(e.kind(), io::ErrorKind::InvalidData);
    }

    #[test]
    fn clones_share_one_record_sequence_in_both_directions() {
        // Writes alternate between a handle and its clone; the peer reads one
        // gap-free sequence. A clone with FRESH counters would seal its record
        // under sequence 1 again and the peer's read would fail to authenticate.
        let a = connect(KEY, KEY);
        let (mut ca, mut sa) = (a.client.unwrap(), a.server.unwrap());
        let mut ca2 = ca.try_clone().unwrap();
        ca.write_all(b"a").unwrap();
        ca2.write_all(b"b").unwrap();
        ca.write_all(b"c").unwrap();
        let mut buf = [0u8; 3];
        sa.read_exact(&mut buf).unwrap();
        assert_eq!(&buf, b"abc");
        // ...and the receive side is shared too: the clone reads what the
        // original has not yet drained, in order.
        let mut sa2 = sa.try_clone().unwrap();
        ca.write_all(b"xyz").unwrap();
        let mut one = [0u8; 1];
        sa.read_exact(&mut one).unwrap();
        assert_eq!(&one, b"x");
        let mut two = [0u8; 2];
        sa2.read_exact(&mut two).unwrap();
        assert_eq!(&two, b"yz");
        // Silence the unused-raw-handle lints: the raws just keep the sockets open.
        drop((a.raw_client, a.raw_server));
    }
}
