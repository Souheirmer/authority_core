//! Trace validation (conformance testing, NOT a refinement proof).
//!
//! Replays TLC simulation traces of model/Provisioning.tla (generated through
//! trace_validation/tla/TraceGen.tla) against the verified authority_core code
//! and compares, after every step and for every device, the code's cache entry
//! (status, ver, orig) with the model's (pdpSt, pdpVer, pdpOrig) and the
//! code's decision with the model's AllowRule(d). See MAPPING.md.
//!
//! Usage: trace_check <mode> <cfg file> <trace dir>
//!   mode = real    verified Cache (A8) against the traces' AllowRule
//!          mutant  receipt-timed RtCache against the traces' AllowRule
//!          poll-as-apply  verified Cache, but poll answers sent through apply
//!                 (the rejected mapping 1(b)); a non-vacuity check of the cache comparison
mod tla;

use authority_core::cache::Cache;
use authority_core::decode::decode;
use authority_core::spec::{Entry, Status, N};
use authority_core_mutants::receipt_timed::RtCache;
use authority_core_mutants::spec as mspec;
use std::collections::BTreeSet;
use tla::{parse_cfg, parse_trace, State, V};

/// Model value d<k> -> device id k-1.
fn dev_id(v: &V) -> u32 {
    let s = v.model();
    let k: u32 = s.strip_prefix('d').expect("device model value d<k>").parse().unwrap();
    assert!(k >= 1 && (k as usize) <= N);
    k - 1
}

fn status_of(model_st: &str) -> Status {
    match model_st {
        "Absent" => Status::Unknown,
        "Enrolled" => Status::Enrolled,
        "Revoked" => Status::Revoked,
        "Suspended" => Status::Suspended,
        s => panic!("unknown registry state {s}"),
    }
}

fn mstatus(s: Status) -> mspec::Status {
    match s {
        Status::Unknown => mspec::Status::Unknown,
        Status::Enrolled => mspec::Status::Enrolled,
        Status::Revoked => mspec::Status::Revoked,
        Status::Suspended => mspec::Status::Suspended,
    }
}

/// Wire encoding (checker helper): status byte, device BE u32, ver BE u64, orig BE u64.
fn encode(st: Status, device: u32, ver: u64, orig: u64) -> [u8; 21] {
    let mut b = [0u8; 21];
    b[0] = match st {
        Status::Revoked => 0,
        Status::Enrolled => 1,
        Status::Suspended => 2,
        Status::Unknown => panic!("Absent/Unknown is not encodable"),
    };
    b[1..5].copy_from_slice(&device.to_be_bytes());
    b[5..13].copy_from_slice(&ver.to_be_bytes());
    b[13..21].copy_from_slice(&orig.to_be_bytes());
    b
}

enum Impl {
    Real(Cache),
    Mutant(RtCache),
}

impl Impl {
    fn entry(&self, d: u32) -> Entry {
        match self {
            Impl::Real(c) => c.entries[d as usize],
            Impl::Mutant(c) => {
                let e = c.entries[d as usize];
                let st = match e.status {
                    mspec::Status::Unknown => Status::Unknown,
                    mspec::Status::Enrolled => Status::Enrolled,
                    mspec::Status::Revoked => Status::Revoked,
                    mspec::Status::Suspended => Status::Suspended,
                };
                Entry { status: st, ver: e.ver, orig: e.orig }
            }
        }
    }
    fn allow(&self, d: u32, now: u64, delta: u64, sigma_hat: u64, critical: bool) -> bool {
        match self {
            Impl::Real(c) => c.allow_device(d, now, delta, sigma_hat, critical),
            Impl::Mutant(c) => c.allow_device(d, now, delta, sigma_hat, critical),
        }
    }
}

#[derive(Default, Debug)]
struct Stats {
    traces: u64,
    steps: u64,
    comparisons: u64,
    delivered: u64,
    polls: u64,
    skipped_absent: u64,
    cache_mismatch_steps: u64,
    decision_mismatch_steps: u64,
    traces_with_mismatch: u64,
    allow_true_checked: u64,
    first_mismatch: Option<String>,
}

struct Consts {
    delta: u64,
    sigma_hat: u64,
    critical: BTreeSet<String>,
    devices: Vec<V>,
}

fn critical_active(s: &State, d: &V, k: &Consts) -> bool {
    s["activeEv"].app(d).set().iter().any(|e| k.critical.contains(e.model()))
}

fn compare(s: &State, imp: &Impl, k: &Consts, st: &mut Stats, ctx: &str) -> bool {
    let now = s["now"].int() as u64;
    let mut ok = true;
    let mut cache_bad = false;
    let mut dec_bad = false;
    for dv in &k.devices {
        let d = dev_id(dv);
        let e = imp.entry(d);
        let m_st = status_of(s["pdpSt"].app(dv).str());
        let m_ver = s["pdpVer"].app(dv).int() as u64;
        let m_orig = s["pdpOrig"].app(dv).int() as u64;
        if e.status != m_st || e.ver != m_ver || e.orig != m_orig {
            cache_bad = true;
            if st.first_mismatch.is_none() {
                st.first_mismatch = Some(format!("{ctx}: cache d{}: code {:?} vs model ({:?},{},{})", d + 1, e, m_st, m_ver, m_orig));
            }
        }
        let code = imp.allow(d, now, k.delta, k.sigma_hat, critical_active(s, dv, k));
        let model = s["allowed"].app(dv).bool();
        st.comparisons += 1;
        if model { st.allow_true_checked += 1; }
        if code != model {
            dec_bad = true;
            if st.first_mismatch.is_none() {
                st.first_mismatch = Some(format!("{ctx}: decision d{} at now={now}: code {code} vs model {model}", d + 1));
            }
        }
    }
    if cache_bad { st.cache_mismatch_steps += 1; ok = false; }
    if dec_bad { st.decision_mismatch_steps += 1; ok = false; }
    ok
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert!(args.len() == 4, "usage: trace_check <real|mutant> <cfg> <trace dir>");
    let mode = args[1].as_str();
    let cfg = parse_cfg(&std::fs::read_to_string(&args[2]).unwrap());
    let k = Consts {
        delta: cfg["LEASE"].int() as u64,
        sigma_hat: cfg["SKEWBOUND"].int() as u64,
        critical: cfg["CRITICAL"].set().iter().map(|e| e.model().to_string()).collect(),
        devices: cfg["DEVICES"].set().to_vec(),
    };
    let mut files: Vec<_> = std::fs::read_dir(&args[3]).unwrap().map(|e| e.unwrap().path()).collect();
    files.sort();
    let mut st = Stats::default();
    for f in &files {
        let states = parse_trace(&std::fs::read_to_string(f).unwrap());
        assert!(!states.is_empty(), "empty trace {f:?}");
        st.traces += 1;
        let mut imp = match mode {
            "real" | "poll-as-apply" => Impl::Real(Cache::new()),
            "mutant" => Impl::Mutant(RtCache::new()),
            _ => panic!("mode must be real, mutant or poll-as-apply"),
        };
        let name = f.file_name().unwrap().to_string_lossy().to_string();
        let mut trace_ok = compare(&states[0], &imp, &k, &mut st, &format!("{name} state 1"));
        for i in 1..states.len() {
            let (pre, post) = (&states[i - 1], &states[i]);
            let act = post["act"].tuple();
            st.steps += 1;
            match act[0].str() {
                "DeliverNotify" => {
                    let m = &act[1];
                    let (dv, mst) = (m.field("dv"), m.field("st").str());
                    let (ver, orig) = (m.field("ver").int() as u64, m.field("orig").int() as u64);
                    if mst == "Absent" {
                        // Provisioning.tla line 565: (st = "Absent") <=> (v = 0)
                        assert_eq!(ver, 0, "{name}: Absent notification with ver {ver}");
                        st.skipped_absent += 1;
                    } else {
                        let bytes = encode(status_of(mst), dev_id(dv), ver, orig);
                        let n = decode(&bytes).expect("encoded notification must decode");
                        match &mut imp {
                            Impl::Real(c) => c.apply(&n),
                            Impl::Mutant(c) => {
                                let mn = mspec::Notification { device: n.device, status: mstatus(n.status), ver: n.ver, orig: n.orig };
                                c.apply(&mn, post["now"].int() as u64)
                            }
                        }
                        st.delivered += 1;
                    }
                }
                "PdpPoll" => {
                    // the registry's answer is the pre-state (reg[d], regVer[d]); stamped with now
                    let dv = &act[1];
                    let (rs, rv, now) = (status_of(pre["reg"].app(dv).str()), pre["regVer"].app(dv).int() as u64, pre["now"].int() as u64);
                    match &mut imp {
                        Impl::Real(c) if mode == "poll-as-apply" => {
                            if rs != Status::Unknown {
                                let n = decode(&encode(rs, dev_id(dv), rv, now)).unwrap();
                                c.apply(&n)
                            }
                        }
                        Impl::Real(c) => c.poll_update(dev_id(dv), rs, rv, now),
                        Impl::Mutant(c) => c.poll_update(dev_id(dv), mstatus(rs), rv, now),
                    }
                    st.polls += 1;
                }
                // no code counterpart: change only model variables the code does not hold,
                // or the clock / critical flag, which are inputs to allow_device
                "RegChange" | "PushNotify" | "DropNotify" | "SyncFromRegistry" | "ObserveEvent"
                | "ClearEvent" | "RecordAccess" | "Tick" | "Partition" | "Heal" => {}
                a => panic!("unknown action {a}"),
            }
            trace_ok &= compare(post, &imp, &k, &mut st, &format!("{name} state {}", i + 1));
        }
        if !trace_ok { st.traces_with_mismatch += 1; }
    }
    println!(
        "RESULT mode={mode} traces={} steps={} comparisons={} allow_true={} delivered={} polls={} skipped_absent={} cache_mismatch_steps={} decision_mismatch_steps={} traces_with_mismatch={}",
        st.traces, st.steps, st.comparisons, st.allow_true_checked, st.delivered, st.polls, st.skipped_absent,
        st.cache_mismatch_steps, st.decision_mismatch_steps, st.traces_with_mismatch
    );
    if let Some(m) = &st.first_mismatch { println!("FIRST_MISMATCH {m}"); }
}
