// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! The client's side of SIGNALS (aterm tracker AF-15): [`Client::signal`], a volatile
//! last-value publish, and [`Client::subscribe_signals`], the stream that reads them
//! ([`SignalSubscription`]). See [`Request::Signal`] for what the broker keeps and for how
//! long.
//!
//! A subscription to signals is its own type, not a [`Subscription`](super::Subscription)
//! with one more [`Event`](super::Event): a signal has no offset and is no record, and a
//! reader of the log never meets one.

use super::{decode_reply_with_bt, refused, Client, RecvBuf};
use crate::proto::{Request, Response};
use std::io::{self, Read, Write};

/// One signal as a reader is sent it: `subject`'s newest value, and the
/// `(producer_id, seq)` its producer put it under.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signal {
    /// The producer that put the value.
    pub producer_id: u64,
    /// The producer's sequence for it: its incarnation, by the producer's own count.
    pub seq: u64,
    /// The subject the value is the current value of.
    pub subject: String,
    /// The value.
    pub body: Vec<u8>,
}

/// What a signal stream carries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SignalEvent {
    /// A subject's newest value.
    Signal(Signal),
    /// The broker is there with nothing more to send: once when the reader has been sent
    /// every current value its filter matches (the values before this first mark are of
    /// unknown age; each signal after it is a put made while the stream was there), then
    /// after each
    /// [`IDLE_MARK`](crate::broker::IDLE_MARK) with nothing sent. A stream silent for
    /// several of those is a dead link.
    Mark,
}

/// A live stream of signals from the broker ([`Client::subscribe_signals`]).
pub struct SignalSubscription<S> {
    stream: S,
    /// What has been read off `stream` and not yet returned: a read that times out part-way
    /// through a frame keeps what arrived, and the next read finishes it.
    rx: RecvBuf,
}

fn signals_not_offered() -> io::Error {
    io::Error::new(io::ErrorKind::Unsupported, "broker did not offer signals")
}

impl<S: Read + Write> Client<S> {
    /// SIGNAL `body` as `subject`'s current value: a volatile last-value publish
    /// ([`Request::Signal`]). The broker appends nothing; it keeps the newest value of the
    /// subject in memory, sends it to every signal stream whose filter matches
    /// ([`subscribe_signals`](Self::subscribe_signals)), and drops it when this connection
    /// ends. Blocks for the acknowledgement.
    ///
    /// Every signal reaches the readers that are there, an unchanged body included, so a
    /// caller republishes on its own timer to stay seen. `seq` is the producer's
    /// incarnation: it must never fall from one incarnation to the next, and a signal from
    /// another connection of the same producer at a lower `seq` than the broker holds is
    /// acknowledged and dropped. So is one at an EQUAL `seq` from a connection older than
    /// the one that holds the subject: a producer that reconnects takes its subjects with
    /// the new connection, and signals a subject from one live connection at a time.
    ///
    /// ON TCP a signal the broker keeps holds this connection to its keepalive
    /// deadline ([`KEEPALIVE_DEADLINE`](crate::KEEPALIVE_DEADLINE)), as a keepalive does:
    /// signal again, or call [`keepalive_if_idle`](Self::keepalive_if_idle), inside each
    /// deadline, or the broker ends the connection and the value with it. The deadline
    /// holds only while this client makes requests: once the connection becomes a stream
    /// ([`subscribe`](Self::subscribe), [`subscribe_signals`](Self::subscribe_signals))
    /// the broker reads it no more, and the values it signalled last as long as that
    /// stream, whose vanished peer only a failing write reveals. Signal on a connection of
    /// its own.
    ///
    /// The latest `Hello` must offer [`supports_signals`](Self::supports_signals):
    /// otherwise the call fails `Unsupported` with nothing written, so the client stays in
    /// step, and the caller carries its value some other way.
    ///
    /// # Errors
    /// `Unsupported`, as above; the socket; a [`BrokerRefusal`](super::BrokerRefusal) (a
    /// bad or reserved subject, a body past
    /// [`MAX_SIGNAL_BODY`](crate::MAX_SIGNAL_BODY), a bound of the table, the producer's
    /// rate limit, a capability that does not grant the publish);
    /// [`AcksOwed`](super::AcksOwed) while pipelined acks are owed.
    pub fn signal(
        &mut self,
        producer_id: u64,
        seq: u64,
        subject: &str,
        body: &[u8],
    ) -> io::Result<()> {
        self.in_step()?;
        if !self.supports_signals() {
            return Err(signals_not_offered());
        }
        self.send(&Request::Signal {
            producer_id,
            seq,
            subject: subject.to_string(),
            body: body.to_vec(),
        })?;
        self.read_mark()?;
        Ok(())
    }

    /// Stream the signals matching `filter` ([`Request::SubscribeSignals`]): the current
    /// value of every matching subject, a mark, then each change as it is put. Consumes the
    /// client (the connection becomes the stream). CONFLATED: a reader that falls behind is
    /// sent each subject's newest value once, never the values it missed.
    ///
    /// A value whose producer's session ended is not withdrawn on the stream; it stops
    /// being sent. A reader that shows values ages them by its own clock. A signal carries
    /// no age: those before the first [`SignalEvent::Mark`] are what the broker held when
    /// the stream began, put at any time before it, so a reader that ages values from
    /// their arrival holds them unconfirmed until their producer's next signal.
    ///
    /// The latest `Hello` must offer [`supports_signals`](Self::supports_signals):
    /// otherwise the call fails `Unsupported` with nothing written. As for
    /// [`subscribe`](Self::subscribe), the refusal drops the client it consumed.
    ///
    /// # Errors
    /// `Unsupported`, as above; the socket; [`AcksOwed`](super::AcksOwed). A bad filter or
    /// a capability that does not contain it is the first event's error.
    pub fn subscribe_signals(mut self, filter: &str) -> io::Result<SignalSubscription<S>> {
        self.in_step()?;
        if !self.supports_signals() {
            return Err(signals_not_offered());
        }
        self.send(&Request::SubscribeSignals {
            filter: filter.to_string(),
        })?;
        Ok(SignalSubscription {
            stream: self.stream,
            rx: self.rx,
        })
    }
}

impl<S: Read + Write> SignalSubscription<S> {
    /// The underlying byte stream, for transport-level control (a timeout, a shutdown) that
    /// does not touch the frame bytes. Do NOT read or write it: the subscription holds the
    /// bytes it has already read.
    pub const fn get_ref(&self) -> &S {
        &self.stream
    }

    /// Block until the next event, a signal or a mark; `Ok(None)` if the broker closes.
    ///
    /// A read that times out part-way through a frame is resumable: the bytes that arrived
    /// stay on the subscription and the next call finishes the frame.
    ///
    /// # Errors
    /// The socket; a [`BrokerRefusal`](super::BrokerRefusal) that ended the stream (a bad
    /// filter, a capability that does not contain it or that lapsed or was revoked); a
    /// frame that is no part of a signal stream.
    pub fn recv_event(&mut self) -> io::Result<Option<SignalEvent>> {
        let Some(p) = self.rx.next_frame(&mut self.stream)? else {
            return Ok(None);
        };
        let (resp, _) = decode_reply_with_bt(&p)?;
        match resp {
            Response::Signal {
                producer_id,
                seq,
                subject,
                body,
            } => Ok(Some(SignalEvent::Signal(Signal {
                producer_id,
                seq,
                subject,
                body,
            }))),
            Response::Mark { .. } => Ok(Some(SignalEvent::Mark)),
            other => Err(refused(other)),
        }
    }

    /// Block until the next signal, skipping marks; `Ok(None)` if the broker closes.
    ///
    /// # Errors
    /// As [`recv_event`](Self::recv_event).
    pub fn recv(&mut self) -> io::Result<Option<Signal>> {
        loop {
            match self.recv_event()? {
                None => return Ok(None),
                Some(SignalEvent::Mark) => {}
                Some(SignalEvent::Signal(signal)) => return Ok(Some(signal)),
            }
        }
    }
}
