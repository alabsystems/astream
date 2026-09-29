//! A blocking client for the broker: connect, publish (awaiting the ack), and
//! subscribe (blocking on each delivery). The blocking calls are what make tests
//! deterministic — a publish round-trips before the next step, and a subscriber's
//! `recv` returns exactly when the next delivery arrives, with no reliance on sleeps
//! or wall-clock.

use crate::proto::{decode_response, encode_request, read_frame, write_frame, Request, Response};
use astream_wire::{Frame, FrameError, HEADER_SIZE};
use std::io::{self, Read, Write};
use std::net::{TcpStream, ToSocketAddrs};
#[cfg(unix)]
use std::os::unix::net::UnixStream;
#[cfg(unix)]
use std::path::Path;
use std::time::Duration;

/// One record as a client sees it: `(offset, subject, body)` — what a `Delivery`
/// carries.
pub type Record = (u64, String, Vec<u8>);

/// The answer to a bounded, NON-TERMINAL read ([`Client::last`], [`Client::fetch`]):
/// the page of records, then the `(next, head)` its closing `Mark` carried. Also the
/// shape of [`Client::last_all`]'s whole-face answer, whose mark is its FIRST page's.
pub type Page = (Vec<Record>, (u64, u64));

/// The most `Last` requests one [`Client::last_walk`] may make before the walk is
/// called a FAILURE rather than an answer.
///
/// A liveness bound, not a size one. Every page moves the resume cursor strictly
/// forward (it is the last subject the broker VISITED, after the one it was sent), so
/// against a conforming broker a walk ends; one that has not ended in this many
/// requests has met something pathological — a peer whose cursor never runs out, an
/// index grown faster than it is walked — and the honest answer to a caller that must
/// not read absence as evidence is an error, not a short list. At the broker's
/// `LAST_PAGE_MAX` rows a page the ceiling is 4096 × 4096 = 16 777 216 rows; pages the
/// index-scan bound cuts short reach it sooner.
pub const LAST_WALK_PAGES_MAX: usize = 4096;

/// What a [`Client::last_walk`] callback answers after each row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Walk {
    /// Deliver the next row, paging on as the answer needs.
    Continue,
    /// That row was the last one wanted: the walk returns at once — the rest of the
    /// page already read is dropped and no further page is asked for — reporting the
    /// row's subject as the cursor that continues it (or no cursor at all, when that
    /// row was the last of an answer the broker said was complete).
    Stop,
}

/// A connection to a broker over a byte stream. Three transports:
///
/// - [`connect`](Client::connect) — a Unix socket, same machine, unsealed (the
///   kernel scopes who can reach the socket path).
/// - [`connect_tcp`](Client::connect_tcp) — PLAINTEXT TCP, multi-machine on a
///   trusted network only: no confidentiality, no peer authentication.
/// - `connect_tcp_sealed` (behind the `aead` feature) — TCP inside an
///   XChaCha20-Poly1305 sealed record layer under a pre-shared key: confidential
///   and authenticated across an untrusted network. `connect_tcp_handshake`
///   (`handshake`) and `connect_tcp_identity` (`identity`) put a forward-secret key
///   agreement in front of the same record layer.
///
/// `S` is the byte stream; any `Read + Write` works (see
/// [`from_stream`](Client::from_stream)), and the Frame protocol is identical on
/// every transport. A caller that picks the transport at RUNTIME uses the free
/// function [`connect`] instead: one [`AnyClient`] for every wire, plus the
/// [`Closer`] that ends it and bounds its I/O.
#[cfg(unix)]
pub struct Client<S = UnixStream> {
    stream: S,
}

/// A connection to a broker over a byte stream. Windows twin: std has no
/// Unix-domain sockets there, so TCP (`connect_tcp`) is the default (and only)
/// transport.
#[cfg(not(unix))]
pub struct Client<S = TcpStream> {
    stream: S,
}

#[cfg(unix)]
impl Client<UnixStream> {
    /// Connect to the broker's Unix socket at `socket_path` (same machine,
    /// unsealed — reachability is scoped by the socket path's permissions).
    pub fn connect(socket_path: impl AsRef<Path>) -> io::Result<Client<UnixStream>> {
        Ok(Client {
            stream: UnixStream::connect(socket_path)?,
        })
    }
}

impl Client<TcpStream> {
    /// Connect to the broker over PLAINTEXT TCP: multi-machine, but for a trusted
    /// network only — the bytes are neither encrypted nor authenticated. For an
    /// untrusted network use `connect_tcp_sealed` (the `aead` feature), which
    /// carries the same protocol inside an authenticated-encryption record layer.
    pub fn connect_tcp(addr: impl ToSocketAddrs) -> io::Result<Client<TcpStream>> {
        Ok(Client {
            stream: dial_tcp(addr, None)?,
        })
    }

    /// [`connect_tcp`](Self::connect_tcp) with a bound on the CONNECT: each address
    /// `addr` resolves to is tried in turn with `TcpStream::connect_timeout`, so a
    /// black-holed address fails `TimedOut` after `timeout` instead of after the OS's
    /// SYN-retry schedule (minutes). The bound is per address, so the worst case is
    /// `timeout` × addresses; the error is the LAST address's. Name resolution itself
    /// is not bounded (std's resolver has no timeout) — an IP-literal `addr` makes
    /// this a hard bound. The stream comes back blocking: this bounds the connect,
    /// not the requests (see [`Closer`] for those).
    ///
    /// # Errors
    /// Every address failed (the last one's error), `addr` resolved to nothing
    /// (`InvalidInput`), or a zero `timeout` (`InvalidInput`, std's own refusal).
    pub fn connect_tcp_timeout(
        addr: impl ToSocketAddrs,
        timeout: Duration,
    ) -> io::Result<Client<TcpStream>> {
        Ok(Client {
            stream: dial_tcp(addr, Some(timeout))?,
        })
    }
}

/// Dial TCP with `TCP_NODELAY` — every request is one small frame that waits for its
/// answer, so Nagle only adds latency. `None` is `TcpStream::connect` exactly (each
/// resolved address under the OS's own connect timeout); `Some(t)` tries each
/// resolved address with `TcpStream::connect_timeout(addr, t)` and answers the first
/// that connects, else the last error.
fn dial_tcp(addr: impl ToSocketAddrs, timeout: Option<Duration>) -> io::Result<TcpStream> {
    let stream = match timeout {
        None => TcpStream::connect(addr)?,
        Some(t) => {
            let mut last = None;
            let mut connected = None;
            for a in addr.to_socket_addrs()? {
                match TcpStream::connect_timeout(&a, t) {
                    Ok(s) => {
                        connected = Some(s);
                        break;
                    }
                    Err(e) => last = Some(e),
                }
            }
            match (connected, last) {
                (Some(s), _) => s,
                (None, Some(e)) => return Err(e),
                (None, None) => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidInput,
                        "could not resolve to any addresses",
                    ))
                }
            }
        }
    };
    stream.set_nodelay(true)?;
    Ok(stream)
}

/// How long the broker may take to complete the SEALED handshake when the caller gave
/// no connect timeout; lifted after it.
#[cfg(feature = "aead")]
const SEALED_HANDSHAKE_TIMEOUT: Duration = Duration::from_secs(5);

/// Run the client half of the sealed handshake over an already-dialed socket, each
/// read bounded by `deadline` so an unresponsive peer cannot hang the connect; the
/// socket is blocking again afterwards.
#[cfg(feature = "aead")]
fn seal_tcp(
    stream: TcpStream,
    key: [u8; astream_aead::KEY_LEN],
    deadline: Duration,
) -> io::Result<astream_aead::SealedStream<TcpStream>> {
    stream.set_read_timeout(Some(deadline))?;
    let stream = astream_aead::SealedStream::handshake_client(stream, key)?;
    stream.get_ref().set_read_timeout(None)?;
    Ok(stream)
}

/// How long the Rung-7 key agreement may take when the caller gave no connect
/// timeout; lifted after it.
#[cfg(feature = "handshake")]
const KEY_AGREEMENT_TIMEOUT: Duration = Duration::from_secs(10);

/// Run the client half of the Rung-7 forward-secret handshake over an already-dialed
/// socket. Its reads AND writes are bounded by `deadline`, so a broken or hostile
/// server cannot hang the client on the key-agreement I/O; reset to blocking after.
#[cfg(feature = "handshake")]
fn agree_tcp(
    stream: TcpStream,
    psk: &[u8; astream_aead::KEY_LEN],
    deadline: Duration,
) -> io::Result<astream_aead::SealedStream<TcpStream>> {
    stream.set_read_timeout(Some(deadline))?;
    stream.set_write_timeout(Some(deadline))?;
    let sealed = astream_aead::client_handshake(stream, psk)?;
    sealed.get_ref().set_read_timeout(None)?;
    sealed.get_ref().set_write_timeout(None)?;
    Ok(sealed)
}

#[cfg(feature = "aead")]
impl Client<astream_aead::SealedStream<TcpStream>> {
    /// Connect to a broker served by [`serve_tcp_sealed`](crate::Broker::serve_tcp_sealed)
    /// over an XChaCha20-Poly1305-sealed transport under the pre-shared `key`. Runs
    /// the sealed handshake before returning — a fresh hello from each side, bound
    /// with the direction and the record sequence into every record's AAD, and a
    /// key-confirming record each way — so a broker that lacks the key is refused
    /// HERE (the connect fails; nothing but an empty confirm was sent under the
    /// key), and a record recorded from any other connection or direction cannot
    /// be replayed into this one. The Frame protocol is unchanged; it just rides
    /// inside an encrypted, ordered record layer. The handshake has a deadline, so
    /// an unresponsive peer cannot hang the connect.
    pub fn connect_tcp_sealed(
        addr: impl ToSocketAddrs,
        key: [u8; astream_aead::KEY_LEN],
    ) -> io::Result<Client<astream_aead::SealedStream<TcpStream>>> {
        let stream = seal_tcp(dial_tcp(addr, None)?, key, SEALED_HANDSHAKE_TIMEOUT)?;
        Ok(Client { stream })
    }
}

#[cfg(feature = "handshake")]
impl Client<astream_aead::SealedStream<TcpStream>> {
    /// Connect to a broker served by [`serve_tcp_handshake`](crate::Broker::serve_tcp_handshake),
    /// running the Rung-7 forward-secret handshake (ephemeral X25519 authenticated
    /// by the pre-shared `psk`) before the Frame protocol. Each connection derives a
    /// fresh session key, so a later `psk` compromise cannot decrypt this session's
    /// recorded traffic. A wrong `psk`, or a peer not speaking the handshake, fails
    /// the connect.
    pub fn connect_tcp_handshake(
        addr: impl ToSocketAddrs,
        psk: [u8; astream_aead::KEY_LEN],
    ) -> io::Result<Client<astream_aead::SealedStream<TcpStream>>> {
        let sealed = agree_tcp(dial_tcp(addr, None)?, &psk, KEY_AGREEMENT_TIMEOUT)?;
        Ok(Client { stream: sealed })
    }
}

#[cfg(feature = "identity")]
impl Client<astream_aead::SealedStream<TcpStream>> {
    /// Connect to a broker served by [`serve_tcp_identity`](crate::Broker::serve_tcp_identity)
    /// with **static public-key identity, no shared secret** (Rung 8). Runs a
    /// mutual signed-DH (SIGMA/Ed25519) handshake: the broker must present exactly
    /// `expected_server` (its pinned host key), and we prove our own `identity`
    /// (which the broker must have allow-listed). The session key comes from the
    /// ephemeral DH alone (forward-secret under identity-key compromise). A wrong
    /// host key, an unauthorized identity, or a bad signature fails the connect.
    pub fn connect_tcp_identity(
        addr: impl ToSocketAddrs,
        identity: astream_aead::IdentityKeypair,
        expected_server: [u8; astream_aead::ID_PUB_LEN],
    ) -> io::Result<Client<astream_aead::SealedStream<TcpStream>>> {
        let stream = TcpStream::connect(addr)?;
        stream.set_nodelay(true)?;
        let hs_timeout = std::time::Duration::from_secs(10);
        stream.set_read_timeout(Some(hs_timeout))?;
        stream.set_write_timeout(Some(hs_timeout))?;
        let sealed = astream_aead::client_identity_handshake(stream, &identity, &expected_server)?;
        sealed.get_ref().set_read_timeout(None)?;
        sealed.get_ref().set_write_timeout(None)?;
        Ok(Client { stream: sealed })
    }
}

impl<S: Read + Write> Client<S> {
    /// Wrap an already-connected byte stream (any `Read + Write`, e.g. a boxed
    /// `dyn` stream chosen at runtime) as a client. The caller has already done
    /// whatever transport setup (nodelay, sealing) the stream needs; this is the
    /// inverse of [`into_stream`](Self::into_stream).
    pub fn from_stream(stream: S) -> Client<S> {
        Client { stream }
    }

    /// Give the underlying byte stream back (e.g. to box it behind a `dyn` trait so
    /// one code path serves every transport). The connection stays open.
    pub fn into_stream(self) -> S {
        self.stream
    }

    /// Ask the broker for this connection's NONCE — the value an [`attach`](Self::attach)
    /// proof is computed over. Answered by a guarded and an unguarded broker alike, so
    /// one client works against either.
    pub fn hello(&mut self) -> io::Result<[u8; 32]> {
        self.send(&Request::Hello)?;
        match self.read_response()? {
            Response::Nonce { nonce } => nonce.as_slice().try_into().map_err(|_| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("broker nonce is {} bytes, expected 32", nonce.len()),
                )
            }),
            other => Err(refused(other)),
        }
    }

    /// Add a grant to this connection's keyring by presenting a PROOF the caller has
    /// already computed over the nonce from [`hello`](Self::hello) — the primitive
    /// under [`attach`](Self::attach), for a caller that holds its tag somewhere this
    /// process cannot reach it (an agent, a signer). Blocks for the acknowledgement
    /// and returns its `(next, head)`; a refused attach is an error HERE, not a
    /// surprise at the next request.
    pub fn attach_with_proof(&mut self, grant: &str, proof: &[u8]) -> io::Result<(u64, u64)> {
        self.send(&Request::Attach {
            grant: grant.to_string(),
            proof: proof.to_vec(),
        })?;
        self.read_mark()
    }

    /// Add the capability `grant`/`tag` to this connection's keyring: `Hello` for the
    /// connection's nonce, then `Attach` carrying `HMAC-SHA256(tag, nonce ‖ grant)` —
    /// a PROOF OF POSSESSION, so the tag never crosses the wire and a captured attach
    /// cannot be replayed onto another connection. Blocks for the acknowledgement and
    /// returns its `(next, head)`.
    ///
    /// `Attach` APPENDS: several narrow grants on one connection are the intended
    /// shape (read one subtree, commit under another, publish as a bound principal in
    /// a third), and each request is authorized existentially over the ring. A
    /// repeated grant string replaces rather than growing it.
    ///
    /// # Errors
    /// The socket errors, or the broker refuses the attach (a proof that does not
    /// verify, a producer-id collision in the binding table, or a full keyring).
    #[cfg(feature = "cap")]
    pub fn attach(&mut self, grant: &str, tag: &[u8]) -> io::Result<(u64, u64)> {
        let tag: [u8; 32] = tag.try_into().map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("capability tag is {} bytes, expected 32", tag.len()),
            )
        })?;
        let nonce = self.hello()?;
        let proof = astream_cap::attach_proof(&tag, &nonce, grant);
        self.attach_with_proof(grant, &proof)
    }

    /// Without the `cap` feature there is no way to compute an attach PROOF: the tag
    /// stays on the client and the wire carries `HMAC-SHA256(tag, nonce ‖ grant)`
    /// instead, which needs the same vetted MAC a guarded broker uses. Build with
    /// `cap` (or compute the proof yourself and call
    /// [`attach_with_proof`](Self::attach_with_proof)).
    #[cfg(not(feature = "cap"))]
    pub fn attach(&mut self, _grant: &str, _tag: &[u8]) -> io::Result<(u64, u64)> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "presenting a capability needs the `cap` feature: an Attach carries a proof of \
             possession (HMAC-SHA256 over the broker's per-connection nonce), never the tag, \
             so the client must be able to compute that MAC",
        ))
    }

    /// Publish `body` to `subject`, deduped by `(producer_id, producer_seq)`. Blocks
    /// for the ack; returns `(offset, deduped)` — `deduped` true means a re-send
    /// returning the original offset.
    pub fn publish(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: &str,
        body: &[u8],
    ) -> io::Result<(u64, bool)> {
        self.send_publish(producer_id, producer_seq, subject, body)?;
        self.recv_publish_ack()
    }

    /// PIPELINED publish (send side): write a publish WITHOUT waiting for its ack, so a
    /// single connection can keep many in flight (they coalesce into one group-commit
    /// fsync at the broker). Pair each `send_publish` with a later
    /// [`recv_publish_ack`](Self::recv_publish_ack) in the SAME order — the broker
    /// streams acks back in request order. Interleave sends and receives within a
    /// bounded window to avoid filling the socket buffers.
    pub fn send_publish(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: &str,
        body: &[u8],
    ) -> io::Result<()> {
        self.send(&Request::Publish {
            producer_id,
            producer_seq,
            subject: subject.to_string(),
            body: body.to_vec(),
        })
    }

    /// PIPELINED publish (receive side): read the next ack in order, returning
    /// `(offset, deduped)`. See [`send_publish`](Self::send_publish).
    pub fn recv_publish_ack(&mut self) -> io::Result<(u64, bool)> {
        match self.read_response()? {
            Response::PublishAck { offset, deduped } => Ok((offset, deduped)),
            other => Err(refused(other)),
        }
    }

    /// The largest in-flight window [`publish_pipelined`](Self::publish_pipelined) will
    /// use, regardless of the requested window. Kept well under the broker's
    /// `PIPELINE_DEPTH` so the interleaved send/recv loop can never wedge the connection
    /// (a window at/above the broker's bound + non-draining could deadlock until the
    /// broker's ack write-timeout).
    pub const MAX_PIPELINE_WINDOW: usize = 512;

    /// Convenience windowed pipeline: publish `bodies` under `producer_id` (seqs
    /// `1..=len`), keeping at most `window` acks outstanding, and return the acks in
    /// order. Far faster than calling [`publish`](Self::publish) in a loop because the
    /// in-flight publishes share group-commit fsyncs — one connection, many in flight.
    /// The effective window is clamped to `[1, MAX_PIPELINE_WINDOW]` so it cannot
    /// out-run the broker's bounded ack queue.
    ///
    /// The first publish that fails — refused by the broker, or unframeable here —
    /// stops the sending, and the error is returned only after the responses of the
    /// publishes already in flight have been read, so the connection stays in step
    /// for the next call. Those publishes may have landed; re-sending the same bodies
    /// under the same `producer_id` dedups them.
    pub fn publish_pipelined(
        &mut self,
        producer_id: u64,
        subject: &str,
        bodies: &[&[u8]],
        window: usize,
    ) -> io::Result<Vec<(u64, bool)>> {
        let window = window.clamp(1, Self::MAX_PIPELINE_WINDOW);
        let mut acks = Vec::with_capacity(bodies.len());
        let mut sent = 0usize;
        let mut received = 0usize;
        let mut failure: Option<io::Error> = None;
        loop {
            // Top the in-flight window back up.
            while failure.is_none() && sent < bodies.len() && sent - received < window {
                match self.send_publish(producer_id, (sent + 1) as u64, subject, bodies[sent]) {
                    Ok(()) => sent += 1,
                    Err(e) => failure = Some(e),
                }
            }
            if received == sent {
                break;
            }
            // Then drain one response (keeps sends and receives interleaved, no
            // deadlock). A transport failure ends the connection, so it ends this too.
            let resp = match self.read_response() {
                Ok(resp) => resp,
                Err(e) => return Err(failure.unwrap_or(e)),
            };
            received += 1;
            match resp {
                Response::PublishAck { offset, deduped } => acks.push((offset, deduped)),
                other => {
                    failure.get_or_insert(refused(other));
                }
            }
        }
        match failure {
            Some(e) => Err(e),
            None => Ok(acks),
        }
    }

    /// REGISTER A LAST WILL on this connection: the record the broker appends on your
    /// behalf when the connection ends, for any reason — a clean close, a crash, a
    /// cable pull the broker eventually notices. Blocks for the acknowledgement and
    /// returns its `(next, head)`.
    ///
    /// One per connection: a second call replaces the first. The will fires as an
    /// ordinary publish under `(producer_id, producer_seq)`, so publishing that key
    /// yourself first makes it a no-op (an exactly-once goodbye), and it is FENCED —
    /// it appends nothing if a record with a higher `producer_seq` from the same
    /// producer has landed since.
    ///
    /// The fence reads sequences BELOW [`ACK_SEQ_BASE`] only: an ack's sequence is
    /// derived from an offset rather than an incarnation, so acking under this producer
    /// id does not suppress this will. For the same reason a `producer_seq` in the
    /// reserved half is REFUSED here — the fence could not protect a will that lives
    /// where it does not look.
    pub fn will(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: &str,
        body: &[u8],
    ) -> io::Result<(u64, u64)> {
        self.send(&Request::Will {
            producer_id,
            producer_seq,
            subject: subject.to_string(),
            body: body.to_vec(),
        })?;
        self.read_mark()
    }

    /// LAST-VALUE query: the most recent record of every subject matching `filter`
    /// whose subject sorts strictly after `after` (`""` for the first page), at most
    /// `max`, in ascending SUBJECT order. Returns the page and the `(next, head)` of
    /// the closing `Mark`.
    ///
    /// `next` pairs with THIS PAGE, and with no other: it is the head this page was
    /// read at, so a `subscribe` from it tails gap-free and dup-free from THIS
    /// snapshot. A PAGED reader must therefore tail from the FIRST page's `next` and
    /// fold newest-wins across the pages — later pages are read at later heads, and
    /// subscribing from the LAST page's `next` silently skips any record that
    /// superseded a value an earlier page already reported.
    ///
    /// The broker CLAMPS `max` and bounds its scan of the subject index, so a short
    /// page — an EMPTY one included — does not mean the answer ended, and this method
    /// has already thrown away the cursor that says whether it did. It is ONE page, and
    /// nothing that must see the whole face should read it as more. Walk instead:
    /// [`last_walk`](Self::last_walk) (streaming, row-bounded, stoppable) or
    /// [`last_all`](Self::last_all) (collected) follow the cursor to the end, keep the
    /// FIRST page's mark, and turn a walk that does not end into an error.
    /// [`last_page`](Self::last_page) is the one-request primitive under them.
    ///
    /// Non-terminal: the connection is fully usable afterwards (this is the one read
    /// verb that does NOT consume the client).
    pub fn last(&mut self, filter: &str, after: &str, max: u32) -> io::Result<Page> {
        self.last_page(filter, after, max)
            .map(|(page, mark, _)| (page, mark))
    }

    /// [`last`](Self::last) with the RESUME CURSOR: `(page, (next, head), resume)`.
    ///
    /// `resume` is the `after` for the next page; an EMPTY `resume` means the broker's
    /// scan reached the end of the filter's range and this was the last page. Page
    /// until it is empty — a page shorter than `max` is NOT the end, because the
    /// broker bounds how many index entries one request may visit (matched or not) as
    /// well as how many rows it may return. [`last_walk`](Self::last_walk) is that loop.
    pub fn last_page(
        &mut self,
        filter: &str,
        after: &str,
        max: u32,
    ) -> io::Result<(Vec<Record>, (u64, u64), String)> {
        self.send(&Request::Last {
            filter: filter.to_string(),
            after: after.to_string(),
            max,
        })?;
        self.read_page_resumable(max)
    }

    /// WALK A LAST-VALUE FACE: [`last_page`](Self::last_page) repeated on its resume
    /// cursor until the broker says the filter's range is exhausted, each row handed to
    /// `on_row` in ascending subject order. This is the one loop that knows how a
    /// `Last` answer ENDS, so a reader that must see every subject — a roster, a halt
    /// list, an escalation view — calls it rather than restating it.
    ///
    /// THE END IS AN EMPTY `resume`, AND NOTHING ELSE. The broker clamps each request
    /// to `LAST_PAGE_MAX` rows and cuts its index scan after `LAST_SCAN_MAX` entries
    /// VISITED, matched or not, so a page shorter than asked — an EMPTY one included —
    /// is not the end of the answer. The walk pages on the cursor, never on the row
    /// count and never on the last row's subject, which an empty page does not have.
    ///
    /// THE MARK IS THE FIRST PAGE'S. Each request pins its own, later head, so the
    /// answer is a UNION of per-page snapshots, not one snapshot. The `(next, head)`
    /// returned is the first request's — the lowest pin, and so the only offset a
    /// `subscribe(next, filter)` can splice on at with no gap: from a later page's
    /// `next`, a record that superseded a value an earlier page already delivered would
    /// never arrive. The reader pays for the splice: a row from page 2..n may carry an
    /// offset AT OR ABOVE the returned `head`, and the tail may supersede a delivered
    /// row, so a reader that tails folds newest-wins and dedups on offset. Rows never
    /// repeat within one walk; the cursor is a strictly increasing subject.
    ///
    /// AND THE ROWS ALONE ARE NOT THE WHOLE FACE. A subject whose newest record lands
    /// at or above a request's pinned head before that request reaches it is OMITTED
    /// from its page rather than answered stale (see [`Request::Last`]); the record
    /// that displaced it arrives on the tail from `next`. The whole face is the rows
    /// PLUS that tail.
    ///
    /// `after` starts the walk strictly after that subject (`""` for the whole face).
    /// `max` bounds the ROWS the whole walk delivers, not one page's, and each request
    /// asks the broker for exactly the rows still owed, so it never works for rows the
    /// caller will not take; `u32::MAX` is the whole face. `max = 0` is the head query:
    /// one request, no rows, the mark.
    ///
    /// `on_row` runs once its row's page has been read to the closing `Mark`, so the
    /// connection is at a frame boundary whenever it runs and stays usable however the
    /// walk ends — [`Walk::Stop`], the row bound, an `on_row` error. Memory is one page,
    /// not the face.
    ///
    /// Returns the first page's `(next, head)` and the CONTINUATION:
    ///
    /// - `None` — the walk delivered the whole answer: the broker's cursor came back
    ///   empty and every row it sent reached `on_row` (a `Stop` on the very last row
    ///   included).
    /// - `Some(after)` — the walk ended early, on [`Walk::Stop`] or on `max`. Pass it
    ///   back as `after` to continue; it is the subject of the last row delivered (or
    ///   this walk's own `after`, if it delivered none), and continuing from it may
    ///   find nothing more. It is an `Option` where `last_page` has an
    ///   empty-means-done `String` because a walk that stopped before its first row
    ///   must be able to say "continue from the start", and that cursor IS `""`.
    ///
    /// # Errors
    ///
    /// A broker or transport failure, including the broker refusing a request; the
    /// first error `on_row` returns, which ends the walk and is returned as is; or a
    /// walk that has not ended within [`LAST_WALK_PAGES_MAX`] requests — because a
    /// caller that cannot tell "no rows" from "I stopped looking" reports an empty
    /// fleet while a node is escalating. Rows delivered before an error WERE
    /// delivered; the error says the answer is incomplete, not that nothing was seen.
    pub fn last_walk(
        &mut self,
        filter: &str,
        after: &str,
        max: u32,
        mut on_row: impl FnMut(Record) -> io::Result<Walk>,
    ) -> io::Result<((u64, u64), Option<String>)> {
        let mut cursor = after.to_string();
        // The continuation if the walk ends early: the last subject DELIVERED, which
        // starts as the walk's own `after` so a walk that delivered nothing hands that
        // back. `clone_from` reuses the buffer, so tracking it costs no allocation per
        // row once it has grown to the longest subject.
        let mut last = cursor.clone();
        let mut remaining = max;
        // The FIRST request's mark; every later page's is dropped (see above).
        let mut first: Option<(u64, u64)> = None;
        for _ in 0..LAST_WALK_PAGES_MAX {
            let ask = remaining;
            let (page, page_mark, resume) = self.last_page(filter, &cursor, ask)?;
            let mark = *first.get_or_insert(page_mark);
            let rows = page.len();
            let mut taken = 0usize;
            let mut stopped = false;
            for row in page {
                if remaining == 0 {
                    // Unreachable against `last_page`, which refuses a page longer
                    // than it asked for; kept so `max` holds whatever reads the page.
                    break;
                }
                remaining -= 1;
                taken += 1;
                last.clone_from(&row.1);
                if on_row(row)? == Walk::Stop {
                    stopped = true;
                    break;
                }
            }
            // `ask > 0`: a head query's empty cursor means "no page", not "complete".
            if resume.is_empty() && taken == rows && ask > 0 {
                return Ok((mark, None));
            }
            if stopped || remaining == 0 {
                return Ok((mark, Some(last)));
            }
            cursor = resume;
        }
        Err(io::Error::other(format!(
            "the last-value walk of {filter} did not end within {LAST_WALK_PAGES_MAX} pages"
        )))
    }

    /// The WHOLE last-value face of `filter`, collected: [`last_walk`](Self::last_walk)
    /// from the first subject with no row bound. Returns every row, in ascending subject
    /// order, and the FIRST page's `(next, head)` — the gap-free splice point for a
    /// `subscribe(next, filter)` that goes on watching the face (fold newest-wins across
    /// the seam; `last_walk` says why).
    ///
    /// `Ok` only for an answer the broker said was complete; a walk past
    /// [`LAST_WALK_PAGES_MAX`] pages is an error, never a short list. Memory is the
    /// whole face; a reader that can act row by row walks instead.
    pub fn last_all(&mut self, filter: &str) -> io::Result<Page> {
        let mut rows = Vec::new();
        let (mark, rest) = self.last_walk(filter, "", u32::MAX, |row| {
            rows.push(row);
            Ok(Walk::Continue)
        })?;
        match rest {
            None => Ok((rows, mark)),
            // Unreachable against a broker that honours its own page clamp (the page
            // bound ends the walk long before u32::MAX rows), and still not a reason
            // to hand back a list that is short without saying so.
            Some(_) => Err(io::Error::other(format!(
                "the last-value face of {filter} did not end within {} rows",
                u32::MAX
            ))),
        }
    }

    /// BOUNDED READ: at most `max` records matching `filter` with offset >= `from`,
    /// scanning at most the broker's [`FETCH_SCAN_MAX`](crate::broker::FETCH_SCAN_MAX)
    /// records. Returns the page and the `(next, head)` of its closing `Mark`; `next`
    /// is the offset AFTER the last record the broker SCANNED, so paging with it
    /// advances even when a page matched nothing. `max = 0` is the head query.
    ///
    /// Non-terminal: unlike `subscribe` it never tails and does not consume the
    /// client — the connection is fully usable afterwards.
    pub fn fetch(&mut self, from: u64, filter: &str, max: u32) -> io::Result<Page> {
        self.send(&Request::Fetch {
            from_offset: from,
            filter: filter.to_string(),
            max,
        })?;
        self.read_page_resumable(max)
            .map(|(page, mark, _)| (page, mark))
    }

    /// Read `Delivery*` then the closing `Mark` of a bounded, non-terminal read,
    /// keeping the `Mark`'s subject cursor.
    ///
    /// The page is buffered before it is returned, so it is bounded by the `max` the
    /// request asked for (the broker never sends more): a peer that keeps sending
    /// deliveries past it is a protocol violation, not a longer page.
    ///
    /// PRECONDITION: no pipelined publish is un-acked on this connection. The broker
    /// flushes pending acks BEFORE the page (they arrive first, in order), so a caller
    /// that owes itself acks must drain them first; the blocking `publish` never does.
    fn read_page_resumable(&mut self, max: u32) -> io::Result<(Vec<Record>, (u64, u64), String)> {
        let mut page = Vec::new();
        loop {
            match self.read_response()? {
                Response::Delivery { .. } if page.len() >= max as usize => {
                    return Err(io::Error::new(
                        io::ErrorKind::InvalidData,
                        format!("broker sent more than the {max} records the page asked for"),
                    ))
                }
                Response::Delivery {
                    offset,
                    subject,
                    body,
                } => page.push((offset, subject, body)),
                Response::Mark { next, head, resume } => return Ok((page, (next, head), resume)),
                other => return Err(refused(other)),
            }
        }
    }

    /// Subscribe to every record matching `filter` from `from_offset`, then live.
    /// Consumes the client (the connection becomes a delivery stream).
    pub fn subscribe(self, from_offset: u64, filter: &str) -> io::Result<Subscription<S>> {
        self.into_subscription(&Request::Subscribe {
            from_offset,
            filter: filter.to_string(),
        })
    }

    /// Durably advance consumer `group`'s committed offset to `upto` (a pure commit).
    /// Blocks for the ack; returns the commit record's offset.
    pub fn commit(&mut self, group: &str, upto: u64) -> io::Result<u64> {
        self.send(&Request::Commit {
            group: group.to_string(),
            upto,
        })?;
        self.recv_publish_ack().map(|(offset, _)| offset)
    }

    /// The read-process-write TRANSACTION: append `out_body` to `out_subject` AND
    /// commit `group` to `upto` atomically (one durable record), deduped by
    /// `(producer_id, producer_seq)`. Returns `(offset, deduped)`.
    #[allow(clippy::too_many_arguments)]
    pub fn process_and_produce(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        out_subject: &str,
        out_body: &[u8],
        group: &str,
        upto: u64,
    ) -> io::Result<(u64, bool)> {
        self.send(&Request::ProcessAndProduce {
            producer_id,
            producer_seq,
            out_subject: out_subject.to_string(),
            out_body: out_body.to_vec(),
            group: group.to_string(),
            upto,
        })?;
        self.recv_publish_ack()
    }

    /// Subscribe as consumer `group`: the broker resumes delivery from the group's
    /// DURABLE committed offset (no client-tracked cursor), then tails live.
    pub fn subscribe_group(self, group: &str, filter: &str) -> io::Result<Subscription<S>> {
        self.into_subscription(&Request::SubscribeGroup {
            group: group.to_string(),
            filter: filter.to_string(),
        })
    }

    /// COUNTERFACTUAL fork-delivery: stream the alternate timeline that results from
    /// forking the topic at `fork_at` and swapping that record for
    /// `(replacement_subject, replacement_body)`, filtered by `filter`. The live log
    /// is unchanged; the snapshot is delivered then the stream ends (`recv` → `None`).
    pub fn fork_subscribe(
        self,
        fork_at: u64,
        replacement_subject: &str,
        replacement_body: &[u8],
        filter: &str,
    ) -> io::Result<Subscription<S>> {
        self.into_subscription(&Request::ForkSubscribe {
            fork_at,
            replacement_subject: replacement_subject.to_string(),
            replacement_body: replacement_body.to_vec(),
            filter: filter.to_string(),
        })
    }

    /// Write one request frame.
    fn send(&mut self, req: &Request) -> io::Result<()> {
        write_frame(&mut self.stream, &encode_request(req))
    }

    /// Read the one response a request is owed. A close is `UnexpectedEof` and an
    /// undecodable payload is `InvalidData`; a broker `Error` is returned AS a
    /// response, because a refusal leaves the stream in step and a transport failure
    /// does not.
    fn read_response(&mut self) -> io::Result<Response> {
        match read_frame(&mut self.stream)? {
            Some(p) => decode_response(&p).ok_or_else(unexpected_response),
            None => Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "broker closed",
            )),
        }
    }

    /// Read the `Mark` that acknowledges an `Attach` or a `Will`: its `(next, head)`.
    fn read_mark(&mut self) -> io::Result<(u64, u64)> {
        match self.read_response()? {
            Response::Mark { next, head, .. } => Ok((next, head)),
            other => Err(refused(other)),
        }
    }

    /// Send a streaming request and hand the connection over to its delivery stream.
    fn into_subscription(mut self, req: &Request) -> io::Result<Subscription<S>> {
        self.send(req)?;
        Ok(Subscription {
            stream: self.stream,
            rx: RecvBuf::default(),
        })
    }
}

fn unexpected_response() -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, "unexpected response")
}

/// The error a response other than the one a request expects becomes: the broker's
/// own refusal message, or a protocol violation.
fn refused(resp: Response) -> io::Error {
    match resp {
        Response::Error { msg, .. } => io::Error::other(msg),
        _ => unexpected_response(),
    }
}

/// Take at most `max` records from a group subscription WITHOUT committing anything.
///
/// Stops early on end-of-stream, or when a read TIMES OUT — so a caller that wants
/// "whatever has arrived within an idle window" sets that window with
/// [`Subscription::set_read_timeout`] first. That method exists on the three
/// transports whose socket is reachable — `Subscription<UnixStream>` (Unix builds),
/// `Subscription<TcpStream>` and (feature `aead`) the sealed
/// `Subscription<SealedStream<TcpStream>>`, which the `handshake` and `identity`
/// transports also produce. An erased [`AnySubscription`] sets it through the
/// [`Closer`] that [`connect`] returned with its client. On any OTHER stream type
/// there is no idle window: bound the socket yourself before subscribing (reach it
/// with [`Subscription::get_ref`]), or this parks in the read until the broker sends
/// something.
///
/// The idle stop is frame-atomic: a timeout that lands part-way through a record
/// keeps that record's bytes on the subscription and resumes it on the next call
/// (see [`Subscription::recv_event`]), so the same `sub` can be taken from again.
/// The records are already durable and the group's cursor has NOT moved, so a
/// caller that dies here sees them again.
pub fn take<S: Read + Write>(sub: &mut Subscription<S>, max: usize) -> io::Result<Vec<Record>> {
    let mut out = Vec::with_capacity(max.min(64));
    while out.len() < max {
        match sub.recv() {
            Ok(Some(rec)) => out.push(rec),
            Ok(None) => break, // the broker closed
            Err(e)
                if matches!(
                    e.kind(),
                    io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                ) =>
            {
                break; // idle: nothing more right now
            }
            Err(e) => return Err(e),
        }
    }
    Ok(out)
}

/// THE TWO-CONNECTION DRAIN: take at most `max` records from `sub` (a group
/// subscription) and then durably commit `group` through the last one on
/// `committer` — a SECOND connection, because `subscribe_group` consumes its client
/// and a group subscription's own connection is a one-way delivery stream. That price
/// is the reason this is a library helper rather than something every caller
/// re-invents.
///
/// The commit happens AFTER the take, so a failure between the two redelivers the
/// records rather than skipping them. But the group has moved past them by the time
/// `drain` returns: a caller that must PROCESS before committing (at-least-once into
/// an idempotent sink) calls [`take`] and commits itself.
///
/// A broker reaps a connection that sends no request within its first-frame timeout
/// ([`FIRST_FRAME_TIMEOUT`](crate::broker::FIRST_FRAME_TIMEOUT) by default), so a
/// FRESH `committer` whose first request is this commit fails if the take runs
/// longer than that. Make one request on it first — an attach, or
/// [`Client::hello`]; on a guarded broker the deadline runs until a capability is
/// accepted, so there only a successful attach does.
///
/// Returns the records; an empty result commits nothing.
pub fn drain<S: Read + Write, C: Read + Write>(
    sub: &mut Subscription<S>,
    committer: &mut Client<C>,
    group: &str,
    max: usize,
) -> io::Result<Vec<Record>> {
    let records = take(sub, max)?;
    if let Some((last, _, _)) = records.last() {
        committer.commit(group, *last)?;
    }
    Ok(records)
}

/// The top half of the producer sequence space, RESERVED for [`ack`].
///
/// Defined by the LOG ([`crate::store::ACK_SEQ_BASE`]) and re-exported here, so the
/// derivation below and the store's last-will fence read one constant: acks occupy
/// sequences at or above this value, ordinary publishes must stay below it, and the
/// fence — which asks whether a producer has been heard from since it registered its
/// will — ignores the reserved half entirely. `asb` enforces the lower half on `--seq`
/// and `--seq-file`.
pub use crate::store::ACK_SEQ_BASE;

/// THE READ-PROCESS-WRITE ACK: append the ack record AND advance `group` past
/// `offset` in ONE durable record, so the answer and the cursor can never disagree.
///
/// The `producer_seq` is [`ACK_SEQ_BASE`]` | offset`, which is what makes a retry
/// idempotent: a repeated ack for the same offset returns `deduped = true`, appends
/// nothing, and re-applies no commit — and it does so whether the retry came through
/// this helper or through `asb ack`, because both derive the key the same way.
///
/// `offset` must be below [`ACK_SEQ_BASE`] (any real log offset is, by many orders of
/// magnitude), and ordinary publishes by the same `producer_id` must stay below it too
/// — `asb` enforces that on `--seq`/`--seq-file`; a library caller must observe it
/// itself. Within those bounds an ack and an ordinary publish by one producer id never
/// share a dedup key.
///
/// An ack does not raise the producer's last-will fence: the reserved half is excluded
/// from `BrokerLog::producer_high_water`, because an ack's sequence is derived from an
/// offset rather than from an incarnation and is above every sequence a will can hold.
/// Acking under a producer id that also holds a will is therefore safe, and a will
/// registered at a sequence in the reserved half is refused.
///
/// Compatibility: an ack written by a version that keyed it on the BARE `offset` sits
/// under a different dedup key, so retrying it through this version appends a second
/// answer record (the monotone group commit is unaffected). Drain a producer's
/// in-flight acks before upgrading it.
pub fn ack<S: Read + Write>(
    client: &mut Client<S>,
    producer_id: u64,
    group: &str,
    offset: u64,
    out_subject: &str,
    out_body: &[u8],
) -> io::Result<(u64, bool)> {
    debug_assert!(
        offset < ACK_SEQ_BASE,
        "an ack's input offset must stay in the lower half of the sequence space"
    );
    client.process_and_produce(
        producer_id,
        ACK_SEQ_BASE | offset,
        out_subject,
        out_body,
        group,
        offset,
    )
}

/// A live delivery stream from the broker.
#[cfg(unix)]
pub struct Subscription<S = UnixStream> {
    stream: S,
    /// What has been read off `stream` and not yet returned; see [`RecvBuf`].
    rx: RecvBuf,
}

/// A live delivery stream from the broker (Windows twin: TCP default, as above).
#[cfg(not(unix))]
pub struct Subscription<S = TcpStream> {
    stream: S,
    /// What has been read off `stream` and not yet returned; see [`RecvBuf`].
    rx: RecvBuf,
}

#[cfg(unix)]
impl Subscription<UnixStream> {
    /// A handle that can end this subscription from ANOTHER thread: `recv` blocks
    /// in a socket read with no timeout, so an owner that wants to stop a tailing
    /// thread (and release the broker-side connection) shuts the socket down through
    /// this closer, which makes the blocked `recv` return `Ok(None)`.
    ///
    /// The closer holds its own handle to the socket, so while it lives, dropping the
    /// subscription alone does NOT close the connection: call
    /// [`close`](SubscriptionCloser::close), or drop both.
    /// The TCP and sealed subscriptions have the same method, returning the same
    /// [`Closer`]; an erased [`AnySubscription`] has no socket left to reach, so its
    /// closer is the one [`connect`] handed back.
    pub fn closer(&self) -> io::Result<SubscriptionCloser> {
        Closer::unix(&self.stream)
    }
}

/// The name [`Closer`] had when only a Unix-socket [`Subscription`] could make one.
/// Kept so code written against it compiles unchanged: it IS [`Closer`], so it also
/// comes from a TCP or sealed subscription and from [`connect`].
pub type SubscriptionCloser = Closer;

/// What a subscription can carry: a record, or the `Mark` that closes a bounded
/// read. [`Subscription::recv`] keeps its signature and SKIPS marks; a caller that
/// needs the cursor reads [`recv_event`](Subscription::recv_event) instead.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    /// One delivered record: `(offset, subject, body)`.
    Delivery {
        offset: u64,
        subject: String,
        body: Vec<u8>,
    },
    /// The end of a bounded read: resume from `next`; `head` is the
    /// subscriber-visible head the answer was read with.
    Mark { next: u64, head: u64 },
}

/// Bytes a subscription asks its stream for per read, and the size its receive
/// buffer returns to after an oversized frame.
const READ_CHUNK: usize = 64 * 1024;

/// A subscription's receive buffer: the bytes read off the stream that no `recv` has
/// returned yet, `buf[start..end]`.
///
/// Frames are parsed out of this buffer rather than read off the stream with
/// `read_exact`, for two reasons. A read can TIME OUT part-way through a frame
/// (`SO_RCVTIMEO`, under [`take`]'s idle window), and `read_exact` drops the bytes it
/// had already consumed when it does, so the next read would parse a body as a
/// header; here those bytes simply stay in the buffer and the next `recv` finishes
/// the frame. And one read takes every queued frame that fits, so a subscriber
/// catching up on a backlog pays one syscall per buffer rather than two per frame.
///
/// The buffer grows by at most [`READ_CHUNK`] per read — with what the peer has
/// actually SENT, never with the length a header declares — so a peer that announces
/// a 16 MiB frame and stalls pins only what it sent.
#[derive(Default)]
struct RecvBuf {
    buf: Vec<u8>,
    start: usize,
    end: usize,
}

impl RecvBuf {
    /// The payload of the next frame; `Ok(None)` when the stream closes at a frame
    /// boundary. A timeout keeps the unfinished frame for the next call; any other
    /// error discards it, since the stream cannot be resumed past one.
    fn next_frame(&mut self, stream: &mut impl Read) -> io::Result<Option<Vec<u8>>> {
        loop {
            match Frame::decode(&self.buf[self.start..self.end]) {
                Ok(Some(d)) => {
                    self.start += d.consumed;
                    if self.start == self.end {
                        self.reset();
                    }
                    return Ok(Some(d.frame.payload));
                }
                Ok(None) => {}
                Err(e) => {
                    self.reset();
                    let msg = match e {
                        FrameError::TooLarge => "frame exceeds cap",
                        _ => "corrupt frame",
                    };
                    return Err(io::Error::new(io::ErrorKind::InvalidData, msg));
                }
            }
            if self.end == self.buf.len() {
                // Full: slide the unfinished frame to the front, and grow only when it
                // already fills the whole buffer.
                self.buf.copy_within(self.start..self.end, 0);
                self.end -= self.start;
                self.start = 0;
                if self.end == self.buf.len() {
                    self.buf.resize(self.end + READ_CHUNK, 0);
                }
            }
            match stream.read(&mut self.buf[self.end..]) {
                Ok(0) => {
                    let partial = self.end - self.start;
                    self.reset();
                    // As `proto::read_frame`: a close inside a header is a close, one
                    // inside a payload is a frame cut short.
                    return if partial < HEADER_SIZE {
                        Ok(None)
                    } else {
                        Err(io::Error::new(
                            io::ErrorKind::UnexpectedEof,
                            "broker closed mid-frame",
                        ))
                    };
                }
                Ok(n) => self.end += n,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => {
                    if !matches!(
                        e.kind(),
                        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                    ) {
                        self.reset();
                    }
                    return Err(e);
                }
            }
        }
    }

    /// Nothing is owed: empty the buffer, and give back whatever an oversized frame
    /// grew it by.
    fn reset(&mut self) {
        self.start = 0;
        self.end = 0;
        if self.buf.len() > READ_CHUNK {
            self.buf.truncate(READ_CHUNK);
            self.buf.shrink_to_fit();
        }
    }
}

impl<S: Read + Write> Subscription<S> {
    /// The underlying byte stream, for transport-level control — a timeout, a
    /// shutdown — that does not touch the record bytes. This is the escape hatch for
    /// a stream type that has no [`set_read_timeout`](Self::set_read_timeout) of its
    /// own: reach the socket through it and bound the read there. (A boxed
    /// [`AnyStream`] cannot be reached this way — erasing it hid the socket — which
    /// is why [`connect`] returns a [`Closer`] alongside it.) Do NOT read or write
    /// the stream itself — a subscription holds the bytes it has already read (the
    /// rest of a frame a timeout interrupted, and frames queued behind it), and
    /// bytes taken from underneath it are gone from the stream it resumes.
    pub fn get_ref(&self) -> &S {
        &self.stream
    }

    /// Block until the next matching delivery; `Ok(None)` if the broker closes.
    /// A `Mark` is SKIPPED (this method's signature is unchanged) — read
    /// [`recv_event`](Self::recv_event) to see it.
    pub fn recv(&mut self) -> io::Result<Option<Record>> {
        loop {
            match self.recv_event()? {
                None => return Ok(None),
                Some(Event::Mark { .. }) => continue,
                Some(Event::Delivery {
                    offset,
                    subject,
                    body,
                }) => return Ok(Some((offset, subject, body))),
            }
        }
    }

    /// Block until the next event — a delivery OR a `Mark`; `Ok(None)` if the broker
    /// closes.
    ///
    /// A read that TIMES OUT part-way through a frame (see
    /// [`set_read_timeout`](Subscription::set_read_timeout)) is resumable, not a
    /// desync: the bytes that arrived stay on the subscription and the next call
    /// completes the frame from where the timeout left it, so the caller sees the
    /// whole record once — never a prefix dropped on the floor and the tail of a body
    /// parsed as the next header. Any other error discards the partial frame; the
    /// stream is not resumable past it.
    pub fn recv_event(&mut self) -> io::Result<Option<Event>> {
        let Some(p) = self.rx.next_frame(&mut self.stream)? else {
            return Ok(None);
        };
        match decode_response(&p).ok_or_else(unexpected_response)? {
            Response::Delivery {
                offset,
                subject,
                body,
            } => Ok(Some(Event::Delivery {
                offset,
                subject,
                body,
            })),
            Response::Mark { next, head, .. } => Ok(Some(Event::Mark { next, head })),
            other => Err(refused(other)),
        }
    }
}

#[cfg(unix)]
impl Subscription<UnixStream> {
    /// Bound how long [`recv`](Self::recv) / [`recv_event`](Self::recv_event) block
    /// with nothing arriving: past it the read returns `WouldBlock`/`TimedOut`, which
    /// is how [`drain`] stops on an idle stream instead of parking forever.
    ///
    /// The timeout is on the SOCKET, so it can land part-way through a record. That
    /// is not a desync: the partial frame stays on the subscription and the next
    /// `recv` finishes it (see [`recv_event`](Self::recv_event)), so the same `sub`
    /// is safe to drain from again.
    pub fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        self.stream.set_read_timeout(d)
    }
}

impl Subscription<TcpStream> {
    /// The TCP twin of [`Subscription::set_read_timeout`].
    pub fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        self.stream.set_read_timeout(d)
    }

    /// The TCP twin of [`Subscription::closer`]: a [`Closer`] on a duplicate of this
    /// subscription's socket, so another thread can end a `recv` parked on it.
    pub fn closer(&self) -> io::Result<Closer> {
        Closer::tcp(&self.stream)
    }
}

#[cfg(feature = "aead")]
impl Subscription<astream_aead::SealedStream<TcpStream>> {
    /// The SEALED twin of [`Subscription::set_read_timeout`] — the same idle window
    /// for a subscription from `connect_tcp_sealed`, `connect_tcp_handshake` or
    /// `connect_tcp_identity` (all three hand back a `SealedStream<TcpStream>`), so
    /// a consumer on the sealed transport can bound [`drain`] too.
    ///
    /// The timeout is set on the TCP socket UNDER the record layer, so it can land
    /// part-way through a sealed record as well as part-way through a frame. Both
    /// layers resume: the record layer keeps its partial record and its sequence
    /// counter (`astream_aead`'s `read_record`), and [`recv_event`](Self::recv_event)
    /// keeps the partial frame.
    pub fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        self.stream.get_ref().set_read_timeout(d)
    }

    /// The SEALED twin of [`Subscription::closer`]. The duplicate is of the TCP
    /// socket UNDER the record layer — never a second `SealedStream`, which would be a
    /// second record sequence over one socket — because shutting that socket down is
    /// what unparks the reader, and it is all the closer needs.
    pub fn closer(&self) -> io::Result<Closer> {
        Closer::tcp(self.stream.get_ref())
    }
}

/// Any byte stream a broker connection can ride, so a caller that picks its transport
/// at RUNTIME — a flag, a config file — has ONE code path per verb rather than one per
/// wire. Blanket-implemented for every `Read + Write + Send` type. `Send` is a
/// supertrait because a subscription is typically pumped by a thread of its own, and
/// every transport this crate builds is `Send`.
pub trait AnyStream: Read + Write + Send {}
impl<T: Read + Write + Send> AnyStream for T {}

/// A [`Client`] whose transport has been erased — what [`connect`] returns.
pub type AnyClient = Client<Box<dyn AnyStream>>;

/// A [`Subscription`] whose transport has been erased — what an [`AnyClient`]'s
/// `subscribe` / `subscribe_group` / `fork_subscribe` return. Its idle window and its
/// shutdown live on the [`Closer`] that came with the client.
pub type AnySubscription = Subscription<Box<dyn AnyStream>>;

/// How a client reaches the broker: the runtime choice [`connect`] dispatches on.
///
/// EVERY VARIANT EXISTS IN EVERY BUILD. The sealed and handshake wires need the `aead`
/// and `handshake` features, but their variants are not cfg-gated: Cargo unifies
/// features ADDITIVELY across a build graph, so a variant that appeared only when some
/// other crate in the graph switched `aead` on would break every exhaustive `match`
/// written against the default build. [`connect`] refuses a transport this build cannot
/// speak with `ErrorKind::Unsupported` naming the missing feature instead — so a config
/// that says "sealed" still parses and still redacts its key, and fails loudly at the
/// one place it matters, never by quietly speaking plaintext.
///
/// Deliberately NOT `#[non_exhaustive]`, for the opposite reason: a caller's exhaustive
/// match over transports (what to serve, what to name) is where a NEW wire should break
/// the build and be decided on, not fall through a wildcard arm into some other wire's
/// behaviour. Static-identity connections (`connect_tcp_identity`) are not a variant:
/// they carry a keypair and a pinned host key rather than a pre-shared key, and no
/// runtime-chosen caller of this enum serves them yet.
///
/// `Debug` NEVER prints a key: it names the variant and says the key is redacted, so a
/// config logged on a bad day does not put the fleet's pre-shared key in a file.
#[derive(Clone)]
pub enum Transport {
    /// A Unix-domain socket at a filesystem path: same machine, unsealed (the socket
    /// path's permissions scope who can reach it). Unix hosts only — elsewhere
    /// [`connect`] refuses it.
    Unix,
    /// PLAINTEXT TCP to `host:port` — a trusted network only (as
    /// [`Client::connect_tcp`]).
    Tcp,
    /// TCP inside the XChaCha20-Poly1305 sealed record layer under this 32-byte
    /// pre-shared key (as `Client::connect_tcp_sealed`; feature `aead`). Boxed so
    /// moving or cloning the config does not copy the key around the stack.
    Sealed(Box<[u8; 32]>),
    /// The sealed wire behind the Rung-7 forward-secret handshake: an ephemeral X25519
    /// key agreement authenticated by this 32-byte pre-shared key (as
    /// `Client::connect_tcp_handshake`; feature `handshake`).
    Handshake(Box<[u8; 32]>),
}

impl std::fmt::Debug for Transport {
    /// The variant, and never the key.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Transport::Unix => "Unix",
            Transport::Tcp => "Tcp",
            Transport::Sealed(_) => "Sealed(<key redacted>)",
            Transport::Handshake(_) => "Handshake(<key redacted>)",
        })
    }
}

/// Ends a connection from outside the thread using it, and bounds how long that
/// thread's I/O may park — the one handle on the SOCKET under a client or subscription
/// whose stream has been erased ([`connect`]) or wrapped (a sealed record layer).
///
/// It holds a DUPLICATE descriptor of the socket. For a sealed or handshake connection
/// that is the TCP socket UNDER the record layer — never a second `SealedStream`, which
/// would be a second record sequence over one socket. Shutdown and the socket timeouts
/// are properties of the socket rather than of a descriptor, so everything done through
/// the closer applies to the connection it came from, and keeps applying after
/// `subscribe` consumes the client. Dropping a closer does nothing to the connection;
/// [`close`](Self::close) is explicit. `Send + Sync`: one closer can be shared (an
/// `Arc`) with a watchdog.
#[derive(Debug)]
pub struct Closer {
    socket: Socket,
}

/// The socket a [`Closer`] duplicated.
#[derive(Debug)]
enum Socket {
    #[cfg(unix)]
    Unix(UnixStream),
    Tcp(TcpStream),
}

impl Closer {
    #[cfg(unix)]
    fn unix(s: &UnixStream) -> io::Result<Closer> {
        Ok(Closer {
            socket: Socket::Unix(s.try_clone()?),
        })
    }

    fn tcp(s: &TcpStream) -> io::Result<Closer> {
        Ok(Closer {
            socket: Socket::Tcp(s.try_clone()?),
        })
    }

    /// Shut the socket down in BOTH directions: a `recv` (or a request's read) parked
    /// on it returns — `Ok(None)` at a frame boundary, an error part-way through one —
    /// and the broker sees the peer go away, which releases its side of the connection
    /// (and fires a registered last will). Idempotent: closing an already-closed socket
    /// is not an error, and nothing is reported.
    pub fn close(&self) {
        let _ = match &self.socket {
            #[cfg(unix)]
            Socket::Unix(s) => s.shutdown(std::net::Shutdown::Both),
            Socket::Tcp(s) => s.shutdown(std::net::Shutdown::Both),
        };
    }

    /// Bound how long a read on this connection parks with nothing arriving:
    /// `SO_RCVTIMEO` on the socket, so it applies to every read the client or
    /// subscription makes from now on (`None` clears it). Past it the read fails
    /// `WouldBlock`/`TimedOut`.
    ///
    /// On a SUBSCRIPTION that is an idle window, and a resumable one: the partial frame
    /// stays on the subscription ([`Subscription::recv_event`]) and the record layer
    /// keeps its partial record, so [`take`] / [`drain`] can stop and come back. On a
    /// request/reply CLIENT it is a deadline and nothing more: a request that timed out
    /// may still be answered late, so the connection is no longer in step with its
    /// replies — drop it and reconnect; do not retry on it. That is what turns a broker
    /// that accepts and never answers from a caller parked forever into an error.
    ///
    /// # Errors
    /// The `setsockopt`; a zero duration is `InvalidInput` (std's own refusal).
    pub fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        match &self.socket {
            #[cfg(unix)]
            Socket::Unix(s) => s.set_read_timeout(d),
            Socket::Tcp(s) => s.set_read_timeout(d),
        }
    }

    /// Bound how long a write on this connection parks on a full send buffer (a broker
    /// that stopped reading): `SO_SNDTIMEO` on the socket, `None` clears it. A write
    /// that times out may have sent PART of a frame, so the connection is no longer
    /// framed: drop it, do not retry on it.
    ///
    /// # Errors
    /// The `setsockopt`; a zero duration is `InvalidInput` (std's own refusal).
    pub fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        match &self.socket {
            #[cfg(unix)]
            Socket::Unix(s) => s.set_write_timeout(d),
            Socket::Tcp(s) => s.set_write_timeout(d),
        }
    }
}

/// Open ONE connection to `endpoint` over `transport` — a socket path for
/// [`Transport::Unix`], `host:port` for the rest — and return it with its transport
/// erased, together with the [`Closer`] that ends it and bounds its I/O.
///
/// The closer is made HERE, at connect time, from a duplicate of the socket under
/// whatever wrapper the transport adds, because once the stream is boxed nothing can
/// reach that socket again — and it outlives the `subscribe` that consumes the client,
/// which is when a caller needs it most (to end a `recv` parked on another thread, or
/// to give a group subscription its idle window).
///
/// `connect_timeout` bounds ESTABLISHING the connection, and nothing after it:
///
/// - **TCP** (all three TCP transports): each address the endpoint resolves to is tried
///   in turn with `TcpStream::connect_timeout` (see
///   [`Client::connect_tcp_timeout`]), so a black-holed address fails `TimedOut` after
///   the bound instead of after the OS's SYN-retry schedule. The bound is per address,
///   and name resolution is not bounded (std's resolver has no timeout): an IP-literal
///   endpoint makes it a hard bound.
/// - **Sealed / handshake**: the bound also REPLACES the built-in deadline on the
///   transport's handshake I/O (5 s sealed, 10 s key agreement), so a peer that accepts
///   and never answers the hello costs `connect_timeout`, not the default.
/// - **Unix**: not applied. std has no bounded Unix-socket connect; a local connect
///   fails at once when nothing listens, and can park only while a LIVE listener's
///   accept backlog is full.
///
/// `None` is exactly each transport's own constructor — [`Client::connect`],
/// [`Client::connect_tcp`], `Client::connect_tcp_sealed`,
/// `Client::connect_tcp_handshake` — including their built-in handshake deadlines.
/// Either way every stream comes back BLOCKING: bound requests and deliveries with
/// [`Closer::set_read_timeout`] / [`Closer::set_write_timeout`]. Every TCP transport
/// gets `TCP_NODELAY`, as every TCP constructor here does.
///
/// # Errors
/// `Unsupported`, naming what is missing, for a transport this build cannot speak
/// ([`Transport::Sealed`] without the `aead` feature, [`Transport::Handshake`] without
/// `handshake`, [`Transport::Unix`] off a unix host); `InvalidInput` for a zero
/// `connect_timeout`; otherwise the connect, the handshake (a broker without the key is
/// refused HERE, not at the first verb), or the descriptor duplication the closer needs.
pub fn connect(
    transport: &Transport,
    endpoint: &str,
    connect_timeout: Option<Duration>,
) -> io::Result<(AnyClient, Closer)> {
    if connect_timeout == Some(Duration::ZERO) {
        // Refused up front so every transport says the same thing: std refuses a zero
        // TCP connect timeout itself, but a Unix connect would silently ignore it.
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "a zero connect timeout bounds nothing: pass None for the OS default, or a positive duration",
        ));
    }
    match transport {
        Transport::Unix => connect_unix(endpoint),
        Transport::Tcp => {
            let s = dial_tcp(endpoint, connect_timeout)?;
            let closer = Closer::tcp(&s)?;
            Ok(erase(s, closer))
        }
        Transport::Sealed(key) => connect_sealed(endpoint, key, connect_timeout),
        Transport::Handshake(key) => connect_handshake(endpoint, key, connect_timeout),
    }
}

/// Box a connected stream behind [`AnyStream`], beside its closer.
fn erase<S: AnyStream + 'static>(stream: S, closer: Closer) -> (AnyClient, Closer) {
    (Client::from_stream(Box::new(stream)), closer)
}

#[cfg(unix)]
fn connect_unix(endpoint: &str) -> io::Result<(AnyClient, Closer)> {
    let s = UnixStream::connect(endpoint)?;
    let closer = Closer::unix(&s)?;
    Ok(erase(s, closer))
}

#[cfg(not(unix))]
fn connect_unix(_endpoint: &str) -> io::Result<(AnyClient, Closer)> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "Transport::Unix needs a unix host (std has no Unix-domain sockets here); use Transport::Tcp",
    ))
}

#[cfg(feature = "aead")]
fn connect_sealed(
    endpoint: &str,
    key: &[u8; 32],
    connect_timeout: Option<Duration>,
) -> io::Result<(AnyClient, Closer)> {
    let stream = dial_tcp(endpoint, connect_timeout)?;
    let sealed = seal_tcp(
        stream,
        *key,
        connect_timeout.unwrap_or(SEALED_HANDSHAKE_TIMEOUT),
    )?;
    let closer = Closer::tcp(sealed.get_ref())?;
    Ok(erase(sealed, closer))
}

/// Without `aead` there is no record layer to seal with, and a sealed transport must
/// never quietly become a plaintext one.
#[cfg(not(feature = "aead"))]
fn connect_sealed(
    _endpoint: &str,
    _key: &[u8; 32],
    _connect_timeout: Option<Duration>,
) -> io::Result<(AnyClient, Closer)> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "Transport::Sealed needs astream-broker built with the `aead` feature",
    ))
}

#[cfg(feature = "handshake")]
fn connect_handshake(
    endpoint: &str,
    psk: &[u8; 32],
    connect_timeout: Option<Duration>,
) -> io::Result<(AnyClient, Closer)> {
    let stream = dial_tcp(endpoint, connect_timeout)?;
    let sealed = agree_tcp(
        stream,
        psk,
        connect_timeout.unwrap_or(KEY_AGREEMENT_TIMEOUT),
    )?;
    let closer = Closer::tcp(sealed.get_ref())?;
    Ok(erase(sealed, closer))
}

/// Without `handshake` there is no key agreement, and falling back to the plain
/// sealed wire would silently drop the forward secrecy the caller asked for.
#[cfg(not(feature = "handshake"))]
fn connect_handshake(
    _endpoint: &str,
    _psk: &[u8; 32],
    _connect_timeout: Option<Duration>,
) -> io::Result<(AnyClient, Closer)> {
    Err(io::Error::new(
        io::ErrorKind::Unsupported,
        "Transport::Handshake needs astream-broker built with the `handshake` feature",
    ))
}

#[cfg(test)]
mod tests {
    use super::{RecvBuf, READ_CHUNK};
    use astream_wire::{Frame, HEADER_SIZE, MAX_PAYLOAD_LEN};
    use std::io::{self, Read};

    /// A stream that plays `script` one read at a time: `Some(n)` hands out the next
    /// `n` bytes (fewer at the end), `None` is a read timeout. Past the script it is
    /// at EOF.
    struct Scripted {
        bytes: Vec<u8>,
        pos: usize,
        script: Vec<Option<usize>>,
        step: usize,
    }

    impl Scripted {
        fn new(bytes: Vec<u8>, script: Vec<Option<usize>>) -> Scripted {
            Scripted {
                bytes,
                pos: 0,
                script,
                step: 0,
            }
        }
    }

    impl Read for Scripted {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            let Some(&step) = self.script.get(self.step) else {
                return Ok(0);
            };
            self.step += 1;
            let Some(n) = step else {
                return Err(io::Error::new(io::ErrorKind::TimedOut, "scripted"));
            };
            let n = n.min(buf.len()).min(self.bytes.len() - self.pos);
            buf[..n].copy_from_slice(&self.bytes[self.pos..self.pos + n]);
            self.pos += n;
            Ok(n)
        }
    }

    fn framed(payloads: &[Vec<u8>]) -> Vec<u8> {
        payloads
            .iter()
            .flat_map(|p| Frame::new(p.clone()).encode().unwrap())
            .collect()
    }

    /// Every frame comes back whole and in order however the bytes are split — with a
    /// timeout after every single byte, or with every frame in one read — and a frame
    /// bigger than the resting buffer gives its growth back.
    #[test]
    fn frames_survive_any_split_and_a_timeout_at_every_byte() {
        let payloads = vec![b"a".to_vec(), vec![], vec![7u8; 70_000], b"z".to_vec()];
        let bytes = framed(&payloads);
        let byte_by_byte = (0..bytes.len()).flat_map(|_| [Some(1), None]).collect();
        let all_at_once = vec![Some(usize::MAX); bytes.len()];
        for script in [byte_by_byte, all_at_once] {
            let mut s = Scripted::new(bytes.clone(), script);
            let mut rx = RecvBuf::default();
            let mut got = Vec::new();
            loop {
                match rx.next_frame(&mut s) {
                    Ok(Some(p)) => got.push(p),
                    Ok(None) => break,
                    Err(e) if e.kind() == io::ErrorKind::TimedOut => continue,
                    Err(e) => panic!("{e}"),
                }
            }
            assert_eq!(got, payloads);
            assert!(rx.buf.len() <= READ_CHUNK);
        }
    }

    /// A close inside a header is a close; inside a payload it is a frame cut short.
    #[test]
    fn a_close_mid_frame_is_classified_like_read_frame() {
        let bytes = framed(&[b"payload".to_vec()]);
        for (cut, clean) in [(0, true), (HEADER_SIZE - 1, true), (HEADER_SIZE + 3, false)] {
            let mut s = Scripted::new(bytes[..cut].to_vec(), vec![Some(usize::MAX)]);
            match RecvBuf::default().next_frame(&mut s) {
                Ok(None) => assert!(clean, "cut at {cut}"),
                Err(e) => {
                    assert!(!clean, "cut at {cut}: {e}");
                    assert_eq!(e.kind(), io::ErrorKind::UnexpectedEof);
                }
                Ok(Some(p)) => panic!("cut at {cut} produced a frame: {p:?}"),
            }
        }
    }

    /// A header declaring more than the cap is refused on the header alone, before a
    /// byte of its payload is buffered.
    #[test]
    fn an_oversized_header_is_refused_before_its_payload_is_read() {
        let mut hdr = Frame::new(vec![]).encode().unwrap();
        hdr[4..8].copy_from_slice(&((MAX_PAYLOAD_LEN + 1) as u32).to_le_bytes());
        let mut s = Scripted::new(hdr, vec![Some(usize::MAX), Some(usize::MAX)]);
        let e = RecvBuf::default().next_frame(&mut s).unwrap_err();
        assert_eq!(e.kind(), io::ErrorKind::InvalidData);
        assert_eq!(s.step, 1, "one read: the header's");
    }
}
