// SPDX-License-Identifier: Apache-2.0
// Copyright 2026 Andrew Yates

//! End-to-end multi-worker distributed workflow and DAG tests over a live TCP/Unix
//! `astream-broker` instance (`docs/ROADMAP.md` "distributed durable execution").

#![cfg(unix)]

use astream_broker::{Broker, Client, Durability};
use astream_engine::{
    encode_dag_record, encode_lease_record, BusRecord, DagSpec, DagStep, DistributedDag,
    DistributedStepOutcome, DistributedWorkflow, WorkflowBus,
};
use std::io;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::Duration;

static NEXT_ID: AtomicU64 = AtomicU64::new(0);

struct BrokerClientBus {
    client: Client<std::net::TcpStream>,
}

impl BrokerClientBus {
    fn connect_tcp(addr: &str) -> io::Result<Self> {
        Ok(Self {
            client: Client::connect_tcp(addr)?,
        })
    }
}

impl WorkflowBus for BrokerClientBus {
    fn publish_record(
        &mut self,
        producer_id: u64,
        producer_seq: u64,
        subject: &str,
        body: &[u8],
    ) -> io::Result<(u64, bool)> {
        self.client
            .publish(producer_id, producer_seq, subject, body)
    }

    fn fetch_records(
        &mut self,
        from_offset: u64,
        filter: &str,
        max: u32,
    ) -> io::Result<(Vec<BusRecord>, (u64, u64))> {
        self.client.fetch_stamped(from_offset, filter, max)
    }
}

struct TempBroker {
    log_path: std::path::PathBuf,
    addr: String,
    handle: Option<astream_broker::BrokerHandle>,
}

impl TempBroker {
    fn start(tag: &str) -> Self {
        let id = NEXT_ID.fetch_add(1, Ordering::Relaxed);
        let pid = std::process::id();
        let log_path = std::env::temp_dir().join(format!("aspump_distwf_{tag}_{pid}_{id}.log"));
        let _ = std::fs::remove_file(&log_path);
        let broker = Broker::open_with(&log_path, Durability::Strict).expect("open Strict broker");
        let handle = broker.serve_tcp("127.0.0.1:0").expect("serve TCP");
        let addr = handle.tcp_addr().expect("tcp addr").to_string();
        Self {
            log_path,
            addr,
            handle: Some(handle),
        }
    }
}

impl Drop for TempBroker {
    fn drop(&mut self) {
        if let Some(mut h) = self.handle.take() {
            h.shutdown();
        }
        let _ = std::fs::remove_file(&self.log_path);
        if let (Some(dir), Some(name)) = (self.log_path.parent(), self.log_path.file_name()) {
            let prefix = format!("{}.", name.to_string_lossy());
            if let Ok(entries) = std::fs::read_dir(dir) {
                for entry in entries.flatten() {
                    if entry.file_name().to_string_lossy().starts_with(&prefix) {
                        let _ = std::fs::remove_file(entry.path());
                    }
                }
            }
        }
    }
}

#[test]
fn distributed_linear_workflow_over_live_broker_resumes_after_worker_crash() {
    let tb = TempBroker::start("linear");
    let mut ran_w1 = Vec::new();
    {
        let bus1 = BrokerClientBus::connect_tcp(&tb.addr).unwrap();
        let mut wf1 = DistributedWorkflow::open(bus1, "/a/wf/linear1", 4, 11).unwrap();
        let err = wf1
            .run(|step, prev| {
                ran_w1.push(step);
                if step == 2 {
                    return Err(io::Error::other("worker 1 crashed mid-step 2"));
                }
                Ok(format!("{}|{step}", String::from_utf8_lossy(prev)).into_bytes())
            })
            .unwrap_err();
        assert!(err.to_string().contains("crashed mid-step 2"));
    }
    assert_eq!(ran_w1, vec![0, 1, 2]);

    let mut ran_w2 = Vec::new();
    let bus2 = BrokerClientBus::connect_tcp(&tb.addr).unwrap();
    let mut wf2 = DistributedWorkflow::open(bus2, "/a/wf/linear1", 4, 22).unwrap();
    assert_eq!(wf2.committed_steps(), 2);
    let outputs = wf2
        .run(|step, prev| {
            ran_w2.push(step);
            Ok(format!("{}|{step}", String::from_utf8_lossy(prev)).into_bytes())
        })
        .unwrap();
    assert_eq!(ran_w2, vec![2, 3], "committed steps 0..2 must not re-run");
    assert_eq!(String::from_utf8_lossy(&outputs[3]), "|0|1|2|3");
}

#[test]
fn multi_worker_distributed_dag_over_live_broker_handles_lease_takeover_and_zombies() {
    let tb = TempBroker::start("dag");
    // 5-node DAG:
    //   0 -> {1, 2, 3} -> 4
    let spec = DagSpec::new(vec![
        DagStep::new(0, vec![]),
        DagStep::new(1, vec![0]),
        DagStep::new(2, vec![0]),
        DagStep::new(3, vec![0]),
        DagStep::new(4, vec![1, 2, 3]),
    ])
    .unwrap();

    // Step 1: Worker 1 executes root node 0.
    let mut w1 = DistributedDag::open(
        BrokerClientBus::connect_tcp(&tb.addr).unwrap(),
        spec.clone(),
        "/a/wf/dag5",
        101,
        5_000,
    )
    .unwrap();
    let r0 = w1
        .claim_and_step_next(|id, parents| {
            assert_eq!(id, 0);
            assert!(parents.is_empty());
            Ok(b"seed".to_vec())
        })
        .unwrap();
    assert!(matches!(
        r0,
        DistributedStepOutcome::ClaimedAndCommitted { node_id: 0, .. }
    ));

    // Step 2: Simulate a crashed worker 999 that acquired a short 40ms lease on node 1
    // and then died before committing!
    let digest_1 = *spec.node_digest(1).unwrap();
    let short_lease = encode_lease_record(1, 999, 40, &digest_1);
    Client::connect_tcp(&tb.addr)
        .unwrap()
        .publish(999, 1, "/a/wf/dag5/lease/1", &short_lease)
        .unwrap();

    // Step 3: Spawn two concurrent worker threads (202 and 303) to execute the remaining
    // branches (nodes 2, 3, expired-lease takeover on 1, and join node 4)!
    let addr_a = tb.addr.clone();
    let spec_a = spec.clone();
    let t_a = thread::spawn(move || {
        let mut wa = DistributedDag::open(
            BrokerClientBus::connect_tcp(&addr_a).unwrap(),
            spec_a,
            "/a/wf/dag5",
            202,
            5_000,
        )
        .unwrap();
        let mut executed = Vec::new();
        while !wa.is_complete() {
            match wa
                .claim_and_step_next(|id, parents| {
                    executed.push(id);
                    if id == 4 {
                        let joined = format!(
                            "{}+{}+{}",
                            String::from_utf8_lossy(parents[0].1),
                            String::from_utf8_lossy(parents[1].1),
                            String::from_utf8_lossy(parents[2].1),
                        );
                        Ok(joined.into_bytes())
                    } else {
                        Ok(format!("{}-n{id}", String::from_utf8_lossy(parents[0].1)).into_bytes())
                    }
                })
                .unwrap()
            {
                DistributedStepOutcome::ClaimedAndCommitted { .. } => {}
                DistributedStepOutcome::AlreadyComplete => break,
                DistributedStepOutcome::WaitingOnPeers { .. } => {
                    thread::sleep(Duration::from_millis(15));
                }
            }
        }
        executed
    });

    let addr_b = tb.addr.clone();
    let spec_b = spec.clone();
    let t_b = thread::spawn(move || {
        let mut wb = DistributedDag::open(
            BrokerClientBus::connect_tcp(&addr_b).unwrap(),
            spec_b,
            "/a/wf/dag5",
            303,
            5_000,
        )
        .unwrap();
        let mut executed = Vec::new();
        while !wb.is_complete() {
            match wb
                .claim_and_step_next(|id, parents| {
                    executed.push(id);
                    if id == 4 {
                        let joined = format!(
                            "{}+{}+{}",
                            String::from_utf8_lossy(parents[0].1),
                            String::from_utf8_lossy(parents[1].1),
                            String::from_utf8_lossy(parents[2].1),
                        );
                        Ok(joined.into_bytes())
                    } else {
                        Ok(format!("{}-n{id}", String::from_utf8_lossy(parents[0].1)).into_bytes())
                    }
                })
                .unwrap()
            {
                DistributedStepOutcome::ClaimedAndCommitted { .. } => {}
                DistributedStepOutcome::AlreadyComplete => break,
                DistributedStepOutcome::WaitingOnPeers { .. } => {
                    thread::sleep(Duration::from_millis(15));
                }
            }
        }
        executed
    });

    let exec_a = t_a.join().unwrap();
    let exec_b = t_b.join().unwrap();
    assert!(
        !exec_a.is_empty() || !exec_b.is_empty(),
        "workers must complete all remaining DAG nodes"
    );

    // Step 4: Stalled zombie worker 999 wakes up late and publishes a conflicting commit
    // for node 1 — canonical earliest-offset commit winner MUST NOT change!
    let zombie_commit = encode_dag_record(1, &digest_1, b"zombie-corrupt-n1");
    Client::connect_tcp(&tb.addr)
        .unwrap()
        .publish(999, 2, "/a/wf/dag5/commit/1", &zombie_commit)
        .unwrap();

    // Fresh observer worker syncs from offset 0 and verifies canonical outputs across 0..5.
    let mut observer = DistributedDag::open(
        BrokerClientBus::connect_tcp(&tb.addr).unwrap(),
        spec,
        "/a/wf/dag5",
        404,
        5_000,
    )
    .unwrap();
    observer.sync().unwrap();
    assert!(observer.is_complete());
    assert_eq!(observer.committed_output(0), Some(&b"seed"[..]));
    assert_eq!(observer.committed_output(1), Some(&b"seed-n1"[..]));
    assert_eq!(observer.committed_output(2), Some(&b"seed-n2"[..]));
    assert_eq!(observer.committed_output(3), Some(&b"seed-n3"[..]));
    assert_eq!(
        observer.committed_output(4),
        Some(&b"seed-n1+seed-n2+seed-n3"[..])
    );
}
