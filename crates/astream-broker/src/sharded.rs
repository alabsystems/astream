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

#[cfg(unix)]
use crate::client::{Event, SubscriptionCloser};
#[cfg(unix)]
use crate::proto::Gap;
#[cfg(unix)]
use crate::Client;
use crate::{Broker, BrokerHandle, Durability};
#[cfg(unix)]
use astream_wire::Filter;
use astream_wire::{assign_partition, PartitionKey};
#[cfg(unix)]
use std::cell::Cell;
#[cfg(unix)]
use std::collections::BTreeMap;
use std::io::{self, Write};
use std::path::Path;
#[cfg(unix)]
use std::sync::mpsc::{self, Receiver};
#[cfg(unix)]
use std::thread::{self, JoinHandle};

#[cfg(clean_islands)]
#[path = "sharded_island.rs"]
mod sharded_island;
#[cfg(not(clean_islands))]
pub use crate::twins::sharded_clamp_index;
#[cfg(clean_islands)]
pub use sharded_island::sharded_clamp_index;

contract_fn! {
    /// Verified check that a shard count is positive (`0 < shards`),
    /// linked via `clean-kernel-defeq` to `sharded_count_nonzero_isl`.
    #[must_use]
    pub fn sharded_count_nonzero(shards: u32) -> bool
    clauses [ensures result == (0 < shards)]
    {
        0 < shards
    }
}

/// The sidecar file (in the log directory and in the socket directory) that records
/// the shard count a deployment was created with.
pub const SHARDS_FILE: &str = "shards";

/// The shard a subject routes to: the canonical partitioner over the subject bytes, so
/// producer and any consumer independently agree with zero coordination.
pub const fn shard_of(subject: &str, shards: u32) -> usize {
    assign_partition(PartitionKey::Keyed(subject.as_bytes()), shards) as usize
}

/// The count recorded in `dir`'s sidecar, `None` if there is none.
fn read_shards_file(dir: &Path) -> io::Result<Option<u32>> {
    let path = dir.join(SHARDS_FILE);
    match std::fs::read(&path) {
        Ok(bytes) => {
            let Ok(s) = core::str::from_utf8(&bytes) else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("{}: unreadable shard count <non-utf8>", path.display()),
                ));
            };
            let Ok(n) = s.trim().parse::<u32>() else {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("{}: unreadable shard count {s:?}", path.display()),
                ));
            };
            Ok(Some(n))
        }
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
    let target = dir.join(SHARDS_FILE);
    let tmp = dir.join(format!("{SHARDS_FILE}.tmp"));
    {
        let mut f = crate::store::create_fresh(&tmp, &mut std::fs::OpenOptions::new())?;
        f.write_all(format!("{shards}\n").as_bytes())?;
        astream_sys::full_sync(&f)?;
    }
    crate::store::rename_path(&tmp, &target)?;
    crate::store::sync_parent_dir(&target)
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
    let digits = name.strip_prefix("shard-")?.strip_suffix(".log")?;
    let Ok(idx) = digits.parse() else {
        return None;
    };
    Some(idx)
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
                let ep = entry.path();
                if let Some(os_name) = ep.file_name() {
                    if let Some(name) = os_name.to_str() {
                        if let Some(i) = shard_log_index(name) {
                            max_index = Some(match max_index {
                                Some(m) => m.max(i),
                                None => i,
                            });
                        }
                    }
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
#[cfg(unix)]
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
        Self::open_opts(dir, shards, crate::OpenOptions::new(durability))
    }

    /// Open `shards` independent broker logs under `dir` using `opts` (capabilities,
    /// at-rest encryption with independent `<shard-i.log>.seal` bindings, anti-rollback,
    /// per-shard residency budgets, health sidecars, and escalation rules).
    pub fn open_opts(
        dir: impl AsRef<Path>,
        shards: u32,
        opts: crate::OpenOptions,
    ) -> io::Result<ShardedBroker> {
        let dir = dir.as_ref();
        std::fs::create_dir_all(dir)?;
        let shards = shards.max(1);
        check_or_record_log_shards(dir, shards)?;
        let mut brokers = Vec::new();
        for i in 0..shards {
            brokers.push(Broker::open_opts(
                dir.join(format!("shard-{i}.log")),
                opts.clone(),
                || Ok(crate::Prepared::Nothing),
            )?);
        }
        Ok(ShardedBroker { brokers, shards })
    }

    /// Borrow the per-shard [`Broker`] at index `shard` (`0..shards()`).
    #[must_use]
    pub fn broker(&self, shard: usize) -> Option<&Broker> {
        self.brokers.get(shard)
    }

    /// Borrow all per-shard [`Broker`] instances in `0..shards()` order.
    #[must_use]
    pub fn brokers(&self) -> &[Broker] {
        &self.brokers
    }

    /// Bind one Unix socket per shard (`shard-<i>.sock`) under `sock_dir` and start
    /// accepting. Each shard runs its own acceptor + writer; there is no cross-shard
    /// lock, so the shards serve fully in parallel. The shard count is written to
    /// `sock_dir/shards` (before any socket appears) so clients can validate theirs.
    #[cfg(unix)]
    pub fn serve(&self, sock_dir: impl AsRef<Path>) -> io::Result<ShardedHandle> {
        let dir = sock_dir.as_ref();
        std::fs::create_dir_all(dir)?;
        write_shards_file(dir, self.shards)?;
        let mut handles = Vec::new();
        for (i, b) in self.brokers.iter().enumerate() {
            handles.push(b.serve(dir.join(format!("shard-{i}.sock")))?);
        }
        Ok(ShardedHandle {
            handles,
            shards: self.shards,
        })
    }

    /// Bind one ephemeral loopback TCP listener (`127.0.0.1:0`) per shard and start
    /// accepting. Cross-platform (including Windows, where Unix sockets are absent)
    /// and immune to the 104-byte `SUN_LEN` path cap.
    pub fn serve_tcp_loopback(&self) -> io::Result<ShardedHandle> {
        let mut handles = Vec::new();
        for b in &self.brokers {
            match b.serve_tcp("127.0.0.1:0") {
                Ok(h) => handles.push(h),
                Err(e) => {
                    for mut started in handles {
                        started.shutdown();
                    }
                    return Err(e);
                }
            }
        }
        Ok(ShardedHandle {
            handles,
            shards: self.shards,
        })
    }

    /// The shard count.
    pub const fn shards(&self) -> u32 {
        self.shards
    }

    /// Bound the decoded records each shard's log keeps resident in memory to about
    /// `per_shard_budget` bytes ([`Broker::set_resident_budget`]).
    pub fn set_resident_budget(&self, per_shard_budget: usize) {
        for b in &self.brokers {
            b.set_resident_budget(per_shard_budget);
        }
    }

    /// Aggregate `(resident records, resident bytes, retained records)` summed across
    /// all shards ([`Broker::residency`]).
    #[must_use]
    pub fn residency(&self) -> (usize, usize, usize) {
        let mut resident = 0usize;
        let mut bytes = 0usize;
        let mut retained = 0usize;
        for b in &self.brokers {
            let (r, rb, ret) = b.residency();
            resident = resident.saturating_add(r);
            bytes = bytes.saturating_add(rb);
            retained = retained.saturating_add(ret);
        }
        (resident, bytes, retained)
    }
}

/// Owns the per-shard [`BrokerHandle`]s; shuts them all down.
pub struct ShardedHandle {
    handles: Vec<BrokerHandle>,
    shards: u32,
}

impl ShardedHandle {
    /// Shut down every shard (each unlinks its socket or closes its TCP listener).
    pub fn shutdown(&mut self) {
        for h in &mut self.handles {
            h.shutdown();
        }
    }

    /// Bound TCP address for `shard` (`0..shards()`) when started via
    /// [`ShardedBroker::serve_tcp_loopback`], or `None` for Unix sockets / out-of-range shard.
    #[must_use]
    pub fn tcp_addr(&self, shard: usize) -> Option<&str> {
        match self.handles.get(shard) {
            Some(h) => h.tcp_addr(),
            None => None,
        }
    }

    /// The shard count.
    pub const fn shards(&self) -> u32 {
        self.shards
    }
}

/// A client that routes by subject across the shards: one connection per shard.
#[cfg(unix)]
pub struct ShardedClient {
    conns: Vec<Client>,
    shards: u32,
}

#[cfg(unix)]
impl ShardedClient {
    /// Connect to all `shards` shard sockets under `sock_dir`. The count is validated
    /// against the directory's `shards` sidecar (written by [`ShardedBroker::serve`]):
    /// a client with the wrong count would route subjects to the wrong shards, so a
    /// mismatch (or a missing sidecar) is refused.
    pub fn connect(sock_dir: impl AsRef<Path>, shards: u32) -> io::Result<ShardedClient> {
        let dir = sock_dir.as_ref();
        let shards = shards.max(1);
        check_sock_shards(dir, shards)?;
        let mut conns = Vec::new();
        for i in 0..shards {
            conns.push(Client::connect(dir.join(format!("shard-{i}.sock")))?);
        }
        Ok(ShardedClient { conns, shards })
    }

    /// The shard a subject routes to (producer and broker agree via the same function).
    pub const fn shard_of(&self, subject: &str) -> usize {
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
        // `shard_of` routes below the shard count, one connection per shard; a route
        // past them is refused rather than trusted.
        let Some(conn) = self.conns.get_mut(s) else {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "subject routes past the shard connections",
            ));
        };
        let (off, deduped) = conn.publish(producer_id, producer_seq, subject, body)?;
        Ok((s, off, deduped))
    }

    /// The shard count.
    pub const fn shards(&self) -> u32 {
        self.shards
    }
}

/// One merged delivery: `(shard, offset, subject, body)`.
#[cfg(unix)]
pub type ShardedDelivery = (usize, u64, String, Vec<u8>);

/// What a fan-in carries: a delivery, or one shard's gap notice
/// ([`Event::Gap`]): retention gave up records of the filter on
/// that shard below its tail, so the records of `gap.from..gap.to` that shard does not
/// deliver are gone. Offsets are per shard, so a notice is only ever that shard's.
#[cfg(unix)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ShardedEvent {
    /// A delivery, as [`ShardedSubscription::recv`] returns it.
    Delivery(ShardedDelivery),
    /// A gap notice from `shard`, before every later delivery of that shard.
    Gap {
        /// The shard whose tail was told.
        shard: usize,
        /// What it was told, in that shard's offsets.
        gap: Gap,
    },
}

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
///
/// Each shard's tail asks for gap notices (R4's addendum, A9), and a notice is forwarded in
/// the shard's order: [`recv_event`](Self::recv_event) returns it, and
/// [`take_gaps`](Self::take_gaps) hands back, shard by shard, every notice a read passed.
#[cfg(unix)]
pub struct ShardedSubscription {
    rx: Receiver<io::Result<ShardedEvent>>,
    closers: Vec<SubscriptionCloser>,
    forwarders: Vec<JoinHandle<()>>,
    /// The notices read since the last [`take_gaps`](Self::take_gaps), each shard's as one
    /// ([`Gap::and`]).
    gaps: Cell<BTreeMap<usize, Gap>>,
}

#[cfg(unix)]
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
            closers: Vec::new(),
            forwarders: Vec::new(),
            gaps: Cell::new(BTreeMap::new()),
        };
        for i in 0..shards {
            let mut sub = Client::connect(dir.join(format!("shard-{i}.sock")))?
                .subscribe(from_offset, filter)?;
            this.closers.push(sub.closer()?);
            let tx = tx.clone();
            let shard = i as usize;
            this.forwarders.push(thread::spawn(move || loop {
                // Forward this shard's deliveries and gap notices, in its order, until the
                // stream ends (broker closed, or our closer shut the socket), the consumer
                // dropped the receiver (send fails), or the shard errors — which is
                // forwarded, tagged with the shard, before this forwarder ends. Marks are
                // the shard's liveness, not the fan-in's: skipped.
                let event = match sub.recv_event() {
                    Ok(Some(Event::Delivery {
                        offset,
                        subject,
                        body,
                    })) => ShardedEvent::Delivery((shard, offset, subject, body)),
                    Ok(Some(Event::Gap(gap))) => ShardedEvent::Gap { shard, gap },
                    Ok(Some(Event::Mark { .. })) => continue,
                    Ok(None) => break,
                    Err(e) => {
                        let _ =
                            tx.send(Err(io::Error::new(e.kind(), format!("shard {shard}: {e}"))));
                        break;
                    }
                };
                if tx.send(Ok(event)).is_err() {
                    break;
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
    ///
    /// A shard's gap notice is SKIPPED (this method's signature is unchanged):
    /// [`take_gaps`](Self::take_gaps) hands back every notice it passed, and
    /// [`recv_event`](Self::recv_event) returns them in order.
    pub fn recv(&self) -> io::Result<Option<ShardedDelivery>> {
        loop {
            match self.recv_event()? {
                Some(ShardedEvent::Delivery(d)) => return Ok(Some(d)),
                Some(ShardedEvent::Gap { .. }) => {}
                None => return Ok(None),
            }
        }
    }

    /// Block for the next merged event: a delivery, or a shard's gap notice, which comes
    /// before every later delivery of its shard. Errors and the end as for
    /// [`recv`](Self::recv).
    pub fn recv_event(&self) -> io::Result<Option<ShardedEvent>> {
        match self.rx.recv() {
            Ok(Ok(ShardedEvent::Gap { shard, gap })) => {
                let mut gaps = self.gaps.take();
                let told = match gaps.get(&shard) {
                    Some(before) => before.and(gap),
                    None => gap,
                };
                gaps.insert(shard, told);
                self.gaps.set(gaps);
                Ok(Some(ShardedEvent::Gap { shard, gap }))
            }
            Ok(Ok(d)) => Ok(Some(d)),
            Ok(Err(e)) => Err(e),
            Err(_) => Ok(None),
        }
    }

    /// Every gap notice read since the last call, by [`recv`](Self::recv) or
    /// [`recv_event`](Self::recv_event), each shard's as one ([`Gap::and`]), in shard
    /// order: what retention gave up below each shard's tail. Empty when none came.
    pub fn take_gaps(&self) -> Vec<(usize, Gap)> {
        self.gaps.take().into_iter().collect()
    }
}

#[cfg(unix)]
impl Drop for ShardedSubscription {
    /// Shut every shard socket (unblocking its forwarder's read) and join the
    /// forwarders, so a dropped fan-in leaves no thread, no client fd, and no
    /// broker-side tail connection behind.
    fn drop(&mut self) {
        for c in &self.closers {
            c.close();
        }
        for h in std::mem::take(&mut self.forwarders) {
            let _ = h.join();
        }
    }
}
