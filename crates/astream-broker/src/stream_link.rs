// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A broker connection over a byte stream someone else already authenticated.
//!
//! The broker listens and dials only over the transports it names itself (Unix, TCP, sealed,
//! handshake, identity). An embedder whose machines already hold one authenticated connection
//! (aterm's fleet TLS link, whose peer key is proved against its membership log) hands a stream
//! of that connection to [`Broker::serve_stream`](crate::Broker::serve_stream), and to a bridge
//! as [`FederationWire::Stream`](crate::FederationWire::Stream), rather than open a second
//! listener with a second identity.
//!
//! The broker needs more of a connection than `Read + Write`: its request loop and its
//! ack-writer run at once on one connection, a tail probes its peer under a read timeout, and
//! shutdown or a revocation must end a thread parked in a read from another thread. So a
//! [`StreamLink`] takes `&self`, and is shared. How one direction reads while the other writes
//! is the implementor's to arrange; a socket gets it from the kernel (the implementations here),
//! and a TLS session from a lock its read does not hold while it waits for bytes.

use crate::client::unless_hung_up;
use std::fmt;
use std::io::{self, Read, Write};
use std::net::{Shutdown, TcpStream};
#[cfg(unix)]
use std::os::unix::net::UnixStream;
use std::sync::Arc;
use std::time::Duration;

/// A full-duplex byte stream, already authenticated by its owner.
///
/// One thread may read while another writes. `shutdown` from any thread wakes a parked read and
/// a parked write, and makes the peer read end of stream: every force-close the broker does
/// ([`Broker::revoke_identity`](crate::Broker::revoke_identity), its shutdown) depends on it.
pub trait StreamLink: Send + Sync + 'static {
    /// Read as [`Read::read`], honouring the timeout [`set_read_timeout`](Self::set_read_timeout)
    /// set (`WouldBlock` or `TimedOut` past it, with no byte lost). `Ok(0)` is end of stream.
    fn read(&self, buf: &mut [u8]) -> io::Result<usize>;
    /// Write as [`Write::write`], honouring [`set_write_timeout`](Self::set_write_timeout).
    fn write(&self, buf: &[u8]) -> io::Result<usize>;
    /// Push out anything the stream buffered, as [`Write::flush`].
    fn flush(&self) -> io::Result<()>;
    /// Bound every later read's wait for bytes; `None` clears it.
    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()>;
    /// Bound every later write's wait for room; `None` clears it.
    fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()>;
    /// Switch to non-blocking reads, or back. A stream that cannot refuses `Unsupported`: the
    /// broker's probe of a tail's peer then waits out the read timeout it armed instead, and a
    /// client's `try_recv_publish_ack` answers `Unsupported`, with the client still framed.
    fn set_nonblocking(&self, _on: bool) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "this stream link has no non-blocking mode",
        ))
    }
    /// Shut down one or both directions. Idempotent; an already closed stream is no error.
    fn shutdown(&self, how: Shutdown) -> io::Result<()>;
}

impl fmt::Debug for dyn StreamLink {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("StreamLink")
    }
}

/// Opens a new [`StreamLink`] to one broker: what a [`FederationWire::Stream`] endpoint dials, on
/// every connection a bridge makes and again on a reconnect. Each call yields its own stream
/// (a logical stream of the embedder's one connection, or a fresh connection).
///
/// [`FederationWire::Stream`]: crate::FederationWire::Stream
pub trait StreamDial: Send + Sync + 'static {
    /// Open one stream to the broker.
    ///
    /// # Errors
    /// Whatever keeps the embedder from opening it.
    fn dial(&self) -> io::Result<Arc<dyn StreamLink>>;
}

/// Sized indirection so `LinkEnd` is a thin `Arc` pointer across `Conn`, `Sock`, and `Socket`.
struct LinkSlot(Arc<dyn StreamLink>);

/// A [`StreamLink`] as the `Read + Write` the frame layer speaks. Clones are ends of one stream.
#[derive(Clone)]
pub(crate) struct LinkEnd(Arc<LinkSlot>);

impl fmt::Debug for LinkEnd {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("LinkEnd")
    }
}

impl LinkEnd {
    pub(crate) fn new(link: Arc<dyn StreamLink>) -> Self {
        Self(Arc::new(LinkSlot(link)))
    }

    pub(crate) fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        let s = &self.0 .0;
        match Some(()).map(|()| s.set_read_timeout(d)) {
            Some(r) => r,
            None => Ok(()),
        }
    }

    pub(crate) fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        let s = &self.0 .0;
        match Some(()).map(|()| s.set_write_timeout(d)) {
            Some(r) => r,
            None => Ok(()),
        }
    }

    pub(crate) fn set_nonblocking(&self, on: bool) -> io::Result<()> {
        let s = &self.0 .0;
        match Some(()).map(|()| s.set_nonblocking(on)) {
            Some(r) => r,
            None => Ok(()),
        }
    }

    pub(crate) fn shutdown(&self, how: Shutdown) -> io::Result<()> {
        let s = &self.0 .0;
        match Some(()).map(|()| s.shutdown(how)) {
            Some(r) => r,
            None => Ok(()),
        }
    }
}

pub(crate) fn dial_stream_link(dialer: &Arc<dyn StreamDial>) -> io::Result<LinkEnd> {
    let link = match Some(()).map(|()| dialer.dial()) {
        Some(r) => r?,
        None => return Err(io::Error::other("unreachable dial state")),
    };
    Ok(LinkEnd::new(link))
}

impl Read for LinkEnd {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let s = &self.0 .0;
        match Some(()).map(|()| s.read(buf)) {
            Some(r) => r,
            None => Ok(0),
        }
    }
}

impl Write for LinkEnd {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let s = &self.0 .0;
        match Some(()).map(|()| s.write(buf)) {
            Some(r) => r,
            None => Ok(0),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        let s = &self.0 .0;
        match Some(()).map(|()| s.flush()) {
            Some(r) => r,
            None => Ok(()),
        }
    }
}

#[cfg(unix)]
impl StreamLink for UnixStream {
    fn read(&self, buf: &mut [u8]) -> io::Result<usize> {
        let mut s = self;
        Read::read(&mut s, buf)
    }

    fn write(&self, buf: &[u8]) -> io::Result<usize> {
        let mut s = self;
        Write::write(&mut s, buf)
    }

    fn flush(&self) -> io::Result<()> {
        Ok(())
    }

    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        unless_hung_up(UnixStream::set_read_timeout(self, d), self)
    }

    fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        unless_hung_up(UnixStream::set_write_timeout(self, d), self)
    }

    fn set_nonblocking(&self, on: bool) -> io::Result<()> {
        UnixStream::set_nonblocking(self, on)
    }

    fn shutdown(&self, how: Shutdown) -> io::Result<()> {
        match UnixStream::shutdown(self, how) {
            Err(e) if e.kind() == io::ErrorKind::NotConnected => Ok(()),
            other => other,
        }
    }
}

impl StreamLink for TcpStream {
    fn read(&self, buf: &mut [u8]) -> io::Result<usize> {
        let mut s = self;
        Read::read(&mut s, buf)
    }

    fn write(&self, buf: &[u8]) -> io::Result<usize> {
        let mut s = self;
        Write::write(&mut s, buf)
    }

    fn flush(&self) -> io::Result<()> {
        Ok(())
    }

    fn set_read_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        unless_hung_up(TcpStream::set_read_timeout(self, d), self)
    }

    fn set_write_timeout(&self, d: Option<Duration>) -> io::Result<()> {
        unless_hung_up(TcpStream::set_write_timeout(self, d), self)
    }

    fn set_nonblocking(&self, on: bool) -> io::Result<()> {
        TcpStream::set_nonblocking(self, on)
    }

    fn shutdown(&self, how: Shutdown) -> io::Result<()> {
        match TcpStream::shutdown(self, how) {
            Err(e) if e.kind() == io::ErrorKind::NotConnected => Ok(()),
            other => other,
        }
    }
}
