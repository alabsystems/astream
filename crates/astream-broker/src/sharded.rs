//! `ShardedBroker` — share-nothing partition sharding (the doctrine's §4.2
//! thread-per-core architecture). N **independent** single-partition brokers, each its
//! own durable log + writer thread + group commit + pipelining, with NO shared lock
//! across shards — so write throughput scales with cores/disks instead of serializing
//! on one writer.
//!
//! Routing is the canonical [`astream_wire::assign_partition`] over the subject, so
//! every record for a subject lands in ONE shard and a subject's order is preserved.
//! The trade-off, stated honestly: ordering is **per-partition**, NOT a global total
//! order across shards (offsets are per-shard) — the same model Kafka uses. The single
//! [`Broker`] remains the globally-ordered option; `ShardedBroker` trades global order
//! for scale.
//!
//! Because routing is a pure function of `(subject, shard count)`, the shard count is
//! part of the data's identity: reopening a directory with a different count would
//! strand the extra shards' acked records and route a subject's new records away from
//! its history. So the count is PERSISTED — a `shards` sidecar file in the log
//! directory, written on first open — and every later open, and every client connect
//! against the socket directory (which gets the same sidecar on `serve`), is validated
//! against it; a mismatch is refused.
//!
//! Each shard is a full [`Broker`], so every per-shard guarantee (exactly-once ingest,
//! Strict durability + crash recovery, group commit, pipelining, fork/cognition verbs)
//! holds within a shard unchanged.
//!
//! Throughput: on a SINGLE disk at Strict durability, sharding does not raise
//! aggregate throughput and can lower it — one optimally-batched log is already
//! fsync-bound, and N shards fragment group commit across N fsync streams contending
//! for the one disk (`broker_sharded_bench`). Sharding pays off across multiple
//! disks/nodes, or where the single writer thread rather than the disk is the
//! bottleneck (the `Relaxed` tier).

use crate::client::SubscriptionCloser;
use crate::{Broker, BrokerHandle, Client, Durability};
use astream_wire::{assign_partition, Filter, PartitionKey};
use std::fs::File;
use std::io::{self, Write};
use std::path::Path;
use std::sync::mpsc::{self, Receiver};
use std::thread::{self, JoinHandle};

/// The sidecar file (in the log directory and in the socket directory) that records
/// the shard count a deployment was created with.
pub const SHARDS_FILE: &str = "shards";

/// The shard a subject routes to: the canonical partitioner over the subject bytes, so
/// producer and any consumer independently agree with zero coordination.
pub fn shard_of(subject: &str, shards: u32) -> usize {
    assign_partition(PartitionKey::Keyed(subject.as_bytes()), shards) as usize
}

/// The count recorded in `dir`'s sidecar, `None` if there is none.
fn read_shards_file(dir: &Path) -> io::Result<Option<u32>> {
    let path = dir.join(SHARDS_FILE);
    match std::fs::read_to_string(&path) {
        Ok(s) => s.trim().parse::<u32>().map(Some).map_err(|_| {
            io::Error::new(
                io::ErrorKind::InvalidData,
                format!("{}: unreadable shard count {s:?}", path.display()),
            )
        }),
        Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
    }
}

/// Record `shards` in `dir`'s sidecar atomically and durably: a temp file, fsync'd,
/// renamed over the sidecar, then the directory fsync'd. A plain `fs::write` can leave
/// an EMPTY sidecar after a power loss (the name durable, the bytes not), which every
/// later open then refuses as an unreadable count; and a reader racing a rewrite
/// could see it half-written.
fn write_shards_file(dir: &Path, shards: u32) -> io::Result<()> {
    let tmp = dir.join(format!("{SHARDS_FILE}.tmp"));
    {
        let mut f = File::create(&tmp)?;
        f.write_all(format!("{shards}\n").as_bytes())?;
        f.sync_all()?;
    }
    std::fs::rename(&tmp, dir.join(SHARDS_FILE))?;
    match File::open(dir).and_then(|d| d.sync_all()) {
        // A filesystem that cannot fsync a directory handle, or a directory this
        // process may write but not open: the file's own bytes are durable, and there
        // is nothing more to do about the entry.
        Err(e)
            if matches!(
                e.kind(),
                io::ErrorKind::Unsupported
                    | io::ErrorKind::InvalidInput
                    | io::ErrorKind::PermissionDenied
            ) =>
        {
            Ok(())
        }
        r => r,
    }
}

fn mismatch(dir: &Path, have: u32, asked: u32) -> io::Error {
    io::Error::new(
        io::ErrorKind::InvalidData,
        format!(
            "shard count mismatch: {} has {have} shards, asked for {asked} \
             (the count is part of the data's routing; reopen with {have})",
            dir.display()
        ),
    )
}

/// The index of a `shard-<i>.log` file name, if it is one.
fn shard_log_index(name: &str) -> Option<u32> {
    name.strip_prefix("shard-")?
        .strip_suffix(".log")?
        .parse()
        .ok()
}

/// Validate `dir`'s recorded shard count against `shards`, recording it on first
/// open. A directory with no sidecar but existing `shard-<i>.log` files (created
/// before the sidecar existed) is validated against those files instead: its count
/// is `max index + 1`, and anything else is a mismatch.
fn check_or_record_log_shards(dir: &Path, shards: u32) -> io::Result<()> {
    match read_shards_file(dir)? {
        Some(have) if have == shards => Ok(()),
        Some(have) => Err(mismatch(dir, have, shards)),
        None => {
            let mut max_index: Option<u32> = None;
            for entry in std::fs::read_dir(dir)? {
                let entry = entry?;
                if let Some(i) = entry.file_name().to_str().and_then(shard_log_index) {
                    max_index = Some(max_index.map_or(i, |m| m.max(i)));
                }
            }
            if let Some(m) = max_index {
                let have = m.saturating_add(1);
                if have != shards {
                    return Err(mismatch(dir, have, shards));
                }
            }
            write_shards_file(dir, shards)
        }
    }
}

/// A client-side check against the socket directory's sidecar (written by `serve`).
fn check_sock_shards(dir: &Path, shards: u32) -> io::Result<()> {
    match read_shards_file(dir)? {
        Some(have) if have == shards => Ok(()),
        Some(have) => Err(mismatch(dir, have, shards)),
        None => Err(io::Error::new(
            io::ErrorKind::NotFound,
            format!(
                "{}: no `{SHARDS_FILE}` sidecar — is a ShardedBroker serving this directory?",
                dir.display()
            ),
        )),
    }
}

/// N independent single-partition brokers under one directory (`shard-<i>.log`).
pub struct ShardedBroker {
    brokers: Vec<Broker>,
    shards: u32,
}

impl ShardedBroker {
    /// Open (creating if absent) `shards` independent Strict broker logs under `dir`.
    pub fn open(dir: impl AsRef<Path>, shards: u32) -> io::Result<ShardedBroker> {
        Self::open_with(dir, shards, Durability::Strict)
    }

    /// Open `shards` independent broker logs under `dir` at the given [`Durability`].
    /// Relaxed + sharding is the regime where sharding actually scales: with no
    /// per-message fsync the single writer thread (not the disk) is the bottleneck, so
    /// independent per-shard writers add real parallelism.
    ///
    /// The count is recorded in `dir/shards` on first open and validated on every
    /// later open: a different count is refused (`InvalidData`) rather than silently
    /// stranding shards and re-routing subjects.
    pub fn open_with(
        dir: impl AsRef<Path>,
        shards: u32,
        durability: Durability,
    ) -> io::Result<ShardedBroker> {
        let dir = dir.as_ref();
        std::fs::create_dir_all(dir)?;
        let shards = shards.max(1);
        check_or_record_log_shards(dir, shards)?;
        let mut brokers = Vec::with_capacity(shards as usize);
        for i in 0..shards {
            brokers.push(Broker::open_with(
                dir.join(format!("shard-{i}.log")),
                durability,
            )?);
        }
        Ok(ShardedBroker { brokers, shards })
    }

    /// Bind one Unix socket per shard (`shard-<i>.sock`) under `sock_dir` and start
    /// accepting. Each shard runs its own acceptor + writer; there is no cross-shard
    /// lock, so the shards serve fully in parallel. The shard count is written to
    /// `sock_dir/shards` (before any socket appears) so clients can validate theirs.
    pub fn serve(&self, sock_dir: impl AsRef<Path>) -> io::Result<ShardedHandle> {
        let dir = sock_dir.as_ref();
        std::fs::create_dir_all(dir)?;
        write_shards_file(dir, self.shards)?;
        let mut handles = Vec::with_capacity(self.shards as usize);
        for (i, b) in self.brokers.iter().enumerate() {
            handles.push(b.serve(dir.join(format!("shard-{i}.sock")))?);
        }
        Ok(ShardedHandle {
            handles,
            shards: self.shards,
        })
    }

    /// The shard count.
    pub fn shards(&self) -> u32 {
        self.shards
    }
}

/// Owns the per-shard [`BrokerHandle`]s; shuts them all down.
pub struct ShardedHandle {
    handles: Vec<BrokerHandle>,
    shards: u32,
}

impl ShardedHandle {
    /// Shut down every shard (each unlinks its socket).
    pub fn shutdown(&mut self) {
        for h in &mut self.handles {
            h.shutdown();
        }
    }

    /// The shard count.
    pub fn shards(&self) -> u32 {
        self.shards
    }
}

/// A client that routes by subject across the shards: one connection per shard.
pub struct ShardedClient {
    conns: Vec<Client>,
    shards: u32,
}

impl ShardedClient {
    /// Connect to all `shards` shard sockets under `sock_dir`. The count is validated
    /// against the directory's `shards` sidecar (written by [`ShardedBroker::serve`]):
    /// a client with the wrong count would route subjects to the wrong shards, so a
    /// mismatch (or a missing sidecar) is refused.
    pub fn connect(sock_dir: impl AsRef<Path>, shards: u32) -> io::Result<ShardedClient> {
        let dir = sock_dir.as_ref();
        let shards = shards.max(1);
        check_sock_shards(dir, shards)?;
        let mut conns = Vec::with_capacity(shards as usize);
        for i in 0..shards {
            conns.push(Client::connect(dir.join(format!("shard-{i}.sock")))?);
        }
        Ok(ShardedClient { conns, shards })
    }

    /// The shard a subject routes to (producer and broker agree via the same function).
    pub fn shard_of(&self, subject: &str) -> usize {
        shard_of(subject, self.shards)
    }

    /// Publish, routed to the subject's shard. Returns the record's PER-SHARD offset and
    /// the deduped flag; `(shard, offset)` together identify the record globally.
    pub fn publish(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: &str,
        body: &[u8],
    ) -> io::Result<(usize, u64, bool)> {
        let s = self.shard_of(subject);
        let (off, deduped) = self.conns[s].publish(producer_id, producer_seq, subject, body)?;
        Ok((s, off, deduped))
    }

    /// The shard count.
    pub fn shards(&self) -> u32 {
        self.shards
    }
}

/// One merged delivery: `(shard, offset, subject, body)`.
pub type ShardedDelivery = (usize, u64, String, Vec<u8>);

/// A fan-in subscription that merges every shard's matching deliveries onto one stream.
/// Ordering is preserved PER SHARD (each shard's records arrive in offset order);
/// across shards the interleaving is arbitrary. A delivery is tagged with its shard, so
/// `(shard, offset)` is a stable identity.
///
/// Per-shard failures are SURFACED, never swallowed: a shard's broker error (e.g. a
/// refused filter) or socket error arrives from [`recv`](Self::recv) as an `Err`
/// naming the shard, and `None` follows once every forwarder has finished — after
/// those `Err`s, so `None` means "no shard is still delivering", not "all ended
/// cleanly".
/// Dropping the subscription closes every shard socket and joins its forwarder
/// thread, so nothing lingers on either side.
pub struct ShardedSubscription {
    rx: Receiver<io::Result<ShardedDelivery>>,
    closers: Vec<SubscriptionCloser>,
    forwarders: Vec<JoinHandle<()>>,
}

impl ShardedSubscription {
    /// Subscribe to `filter` on EVERY shard from `from_offset`, merging deliveries. Each
    /// shard gets its own connection + a forwarder thread that pushes its deliveries onto
    /// the shared channel. The count is validated against the socket directory's
    /// sidecar and the filter against the `astream_wire` grammar, so both fail here
    /// rather than as a silently empty stream; a failure part-way through cleans up
    /// the shards already connected.
    pub fn subscribe_all(
        sock_dir: impl AsRef<Path>,
        shards: u32,
        from_offset: u64,
        filter: &str,
    ) -> io::Result<ShardedSubscription> {
        let dir = sock_dir.as_ref();
        let shards = shards.max(1);
        check_sock_shards(dir, shards)?;
        if let Err(e) = Filter::new(filter) {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("bad filter {filter:?}: {e}"),
            ));
        }
        let (tx, rx) = mpsc::channel();
        // Built incrementally so an early `?` drops a partial subscription, whose
        // Drop closes + joins whatever was already spawned.
        let mut this = ShardedSubscription {
            rx,
            closers: Vec::with_capacity(shards as usize),
            forwarders: Vec::with_capacity(shards as usize),
        };
        for i in 0..shards {
            let mut sub = Client::connect(dir.join(format!("shard-{i}.sock")))?
                .subscribe(from_offset, filter)?;
            this.closers.push(sub.closer()?);
            let tx = tx.clone();
            let shard = i as usize;
            this.forwarders.push(thread::spawn(move || loop {
                // Forward this shard's deliveries until the stream ends (broker
                // closed, or our closer shut the socket), the consumer dropped the
                // receiver (send fails), or the shard errors — which is forwarded,
                // tagged with the shard, before this forwarder ends.
                match sub.recv() {
                    Ok(Some((off, subject, body))) => {
                        if tx.send(Ok((shard, off, subject, body))).is_err() {
                            break;
                        }
                    }
                    Ok(None) => break,
                    Err(e) => {
                        let _ =
                            tx.send(Err(io::Error::new(e.kind(), format!("shard {shard}: {e}"))));
                        break;
                    }
                }
            }));
        }
        Ok(this)
    }

    /// Block for the next merged delivery `(shard, offset, subject, body)`.
    /// `Ok(None)` once every shard's forwarder has FINISHED — AFTER each failing
    /// shard's `Err` has already been yielded, so a caller that ignores `Err`s must
    /// NOT read `None` as a clean fan-in (every shard's broker dying yields N `Err`s
    /// and then `None`); an `Err` names the shard and the other shards keep
    /// delivering, so a caller may continue if partial fan-in is acceptable.
    pub fn recv(&self) -> io::Result<Option<ShardedDelivery>> {
        match self.rx.recv() {
            Ok(Ok(d)) => Ok(Some(d)),
            Ok(Err(e)) => Err(e),
            Err(_) => Ok(None),
        }
    }
}

impl Drop for ShardedSubscription {
    /// Shut every shard socket (unblocking its forwarder's read) and join the
    /// forwarders, so a dropped fan-in leaves no thread, no client fd, and no
    /// broker-side tail connection behind.
    fn drop(&mut self) {
        for c in &self.closers {
            c.close();
        }
        for h in self.forwarders.drain(..) {
            let _ = h.join();
        }
    }
}
