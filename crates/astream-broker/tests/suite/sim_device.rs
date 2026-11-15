// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! Evidence for the EMBEDDER'S POWER-LOSS SEAM ([`SimDevice`], aterm critic item F10): a
//! real [`Broker`] opened over the simulated device by a crate outside astream — this
//! suite links the library without `cfg(test)`, with debug assertions on, as an
//! embedder's tests do — and every power-loss image of it reopened by
//! [`BrokerLog::open_sim`].
//!
//! What an embedder relies on, checked here through the public surface alone:
//!
//! 1. every image opens (P1) and recovers byte-for-byte a PREFIX of what was acked (P2),
//!    never a record below the durable head the broker claimed (P3), and an image that
//!    lost an acked record moved the identity (P4);
//! 2. a batch whose write fails half-way ([`InjectedFaults::write`]) is rolled back
//!    whole on every tier: refused, nothing of it visible, the log not poisoned, its
//!    resend landing at the offset it would have taken — and no power-loss image after
//!    the rollback holds the refused copy.
//!
//! Not vacuous: on each weak tier some image loses an acked record, and on Strict none
//! does. The law itself, on every crash point of the writer and the open with its
//! negative controls, is the crash simulation's (`src/crash_sim.rs`), whose sweeps open
//! through this same [`BrokerLog::open_sim`].

#![cfg(unix)]

use astream_broker::{
    Boot, Broker, BrokerHandle, BrokerLog, Client, Durability, InjectedFaults, LogIdentity,
    OpenOptions, SimDevice, Volume,
};
use astream_wire::Offset;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT: AtomicU64 = AtomicU64::new(0);

/// The boot a run serves in, and the one a power loss leaves.
const BOOT_A: [u8; 16] = [0xA1; 16];
const BOOT_B: [u8; 16] = [0xB2; 16];

/// The tiers, Ordered with no horizon: nothing but the open and a clean close flushes a
/// weak log in full, so what a power loss may take is every acked record.
const TIERS: [Durability; 3] = [
    Durability::Strict,
    Durability::Ordered { horizon: None },
    Durability::Relaxed,
];

/// An exclusive directory under `/tmp` for the socket alone (the log is on the
/// simulated device), removed on drop.
struct Scratch(PathBuf);

impl Scratch {
    fn new() -> Scratch {
        use std::os::unix::fs::DirBuilderExt;
        let mut builder = std::fs::DirBuilder::new();
        builder.mode(0o700);
        for _ in 0..1024 {
            let n = NEXT.fetch_add(1, Ordering::Relaxed);
            let p = PathBuf::from(format!("/tmp/asbsim-{}-{n}", std::process::id()));
            match builder.create(&p) {
                Ok(()) => return Scratch(p),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(e) => panic!("create scratch: {e}"),
            }
        }
        panic!("no exclusive scratch name");
    }

    fn sock(&self) -> PathBuf {
        self.0.join("b.sock")
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn opts(tier: Durability, boot: [u8; 16]) -> OpenOptions {
    let mut o = OpenOptions::new(tier);
    o.boot = Boot::Known(boot);
    o.volume = Volume::Boot;
    o
}

/// A broker over `dev`, served on the scratch socket.
fn serve(dev: &SimDevice, tier: Durability, s: &Scratch) -> (Broker, BrokerHandle) {
    let b = Broker::open_sim(dev, opts(tier, BOOT_A)).expect("a broker opens on the device");
    let h = b.serve(s.sock()).expect("the broker serves");
    (b, h)
}

/// Stop the broker as a killed process would (no clean close).
fn kill(b: Broker, mut h: BrokerHandle) {
    b.arm_unclean_stop();
    h.shutdown();
    drop(b);
}

/// What the next boot's open recovers from one image: the records' subjects and
/// bodies, and the identity.
fn recover(img: &SimDevice, tier: Durability) -> (Vec<(String, Vec<u8>)>, LogIdentity) {
    let log = BrokerLog::open_sim(img, opts(tier, BOOT_B))
        .unwrap_or_else(|e| panic!("{tier:?}: a power-loss image refused (P1): {e}"));
    let recs = log
        .read_from(Offset::ZERO)
        .iter()
        .map(|r| (r.subject.clone(), r.body.clone()))
        .collect();
    (recs, log.identity())
}

/// EVERY POWER-LOSS IMAGE OF AN EMBEDDER'S BROKER RECOVERS AN ACKED PREFIX, AND MOVES
/// ITS IDENTITY WHEN IT LOST ONE: six records, each its own batch, then a kill, then
/// each image opened in the next boot.
#[test]
fn every_power_loss_image_recovers_an_acked_prefix_moving_the_identity_for_a_loss() {
    for tier in TIERS {
        let s = Scratch::new();
        let dev = SimDevice::new(16);
        let (b, h) = serve(&dev, tier, &s);
        let mut c = Client::connect(s.sock()).expect("connect");
        let written: Vec<(String, Vec<u8>)> = (0..6u64)
            .map(|i| (format!("/t/{i}"), format!("record {i}").into_bytes()))
            .collect();
        for (i, (subject, body)) in (0u64..).zip(&written) {
            assert_eq!(c.publish(1, i + 1, subject, body).unwrap(), (i, false));
        }
        let durable = usize::try_from(b.durable_head()).unwrap();
        let identity = b.log_identity();
        drop(c);
        kill(b, h);
        let (images, _) = dev.power_loss_images(64, 0xF10);
        assert!(!images.is_empty(), "{tier:?}: no image");
        let mut lost = 0usize;
        for img in &images {
            let (recs, now) = recover(img, tier);
            let k = recs.len();
            assert!(
                k <= written.len() && recs[..] == written[..k],
                "{tier:?}: an image recovered no prefix of what was acked (P2): {recs:?}"
            );
            assert!(
                k >= durable,
                "{tier:?}: {k} kept below the durable {durable} (P3)"
            );
            if k < written.len() {
                lost += 1;
                assert_ne!(
                    now, identity,
                    "{tier:?}: lost {k}.. and kept its identity (P4)"
                );
            }
        }
        if tier == Durability::Strict {
            assert_eq!(lost, 0, "Strict: a power loss lost an acked record");
        } else {
            assert!(
                lost > 0,
                "{tier:?}: no image lost a record: the sweep is vacuous"
            );
        }
    }
}

/// A WRITE THAT FAILS HALF-WAY ROLLS ITS BATCH BACK WHOLE, ON EVERY TIER: the publish is
/// refused, a fetch sees nothing of it, the log is not poisoned, the resend lands at
/// the offset the refused one would have taken, and no power-loss image after it holds
/// the refused copy twice or past its place.
#[test]
fn a_write_that_fails_half_way_rolls_its_batch_back_whole_on_every_tier() {
    for tier in TIERS {
        let s = Scratch::new();
        let dev = SimDevice::new(16);
        let (b, h) = serve(&dev, tier, &s);
        let mut c = Client::connect(s.sock()).expect("connect");
        assert_eq!(c.publish(1, 1, "/t/a", b"kept").unwrap(), (0, false));
        b.inject_faults(InjectedFaults {
            write: true,
            sync: false,
            truncate: false,
        });
        let refused = c
            .publish(1, 2, "/t/b", b"refused once")
            .expect_err("a publish whose write fails is refused");
        assert!(
            refused.to_string().contains("commit failed"),
            "{tier:?}: refused as {refused}"
        );
        b.inject_faults(InjectedFaults::default());
        let (page, (_, head)) = c.fetch(0, "/t/>", 16).expect("fetch");
        assert_eq!(
            (page.len(), head),
            (1, 1),
            "{tier:?}: the rolled-back batch is visible: {page:?}"
        );
        assert_eq!(
            c.publish(1, 2, "/t/b", b"refused once").unwrap(),
            (1, false),
            "{tier:?}: the resend lands where the refused write would have"
        );
        assert_eq!(c.fetch(0, "/t/>", 16).expect("fetch").0.len(), 2);
        drop(c);
        kill(b, h);
        let written = [
            ("/t/a".to_string(), b"kept".to_vec()),
            ("/t/b".to_string(), b"refused once".to_vec()),
        ];
        let (images, _) = dev.power_loss_images(64, 0xF10);
        for img in &images {
            let (recs, _) = recover(img, tier);
            assert!(
                recs.len() <= written.len() && recs[..] == written[..recs.len()],
                "{tier:?}: an image after the rollback recovered {recs:?}"
            );
        }
    }
}

/// A simulated log keeps no health sidecar: the open asking for one is refused.
#[test]
fn a_broker_on_a_simulated_device_refuses_a_health_sidecar() {
    let mut o = opts(Durability::Strict, BOOT_A);
    o.health_every = Some(std::time::Duration::from_secs(60));
    let err = Broker::open_sim(&SimDevice::new(16), o)
        .err()
        .expect("the open is refused");
    assert_eq!(err.kind(), std::io::ErrorKind::InvalidInput);
}
