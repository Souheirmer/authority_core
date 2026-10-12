//! Extension A: the 50 ✗ cells as Rust tests. Each trace is the one Verus
//! checks in src/rules_cex.rs, replayed on an executable copy of the
//! transition system of src/system_spec.rs (this test file is NOT verified;
//! it panics if any action is not enabled). Decisions use the verified
//! executable rules (src/rules_exec.rs). Configuration: paper_params
//! (one device, one event type e1 = CRITICAL, LEASE 1, MAXAGE 3, MAXVER 2,
//! MAXNET 1, MAXUSE 1, MAXBAD 3, MAXT 3, SKEW = SKEWBOUND = 0).

use authority_core::rules_exec::{exec_allow_rule, RuleConsts, RuleInputs};
use authority_core::rules_spec::Rule;
use authority_core::system_spec::{DevSt, Link, RegSt};

const LEASE: u64 = 1;
const MAXAGE: u64 = 3;
const MAXVER: u64 = 2;
const MAXNET: usize = 1;
const MAXUSE: u64 = 1;
const MAXBAD: u64 = 3;
const MAXT: u64 = 3;
const SKEW: i64 = 0;
const SKEWBOUND: u64 = 0;

fn eq(a: &RegSt, b: &RegSt) -> bool { std::mem::discriminant(a) == std::mem::discriminant(b) }
fn copy(a: &RegSt) -> RegSt {
    match a { RegSt::Absent => RegSt::Absent, RegSt::Enrolled => RegSt::Enrolled, RegSt::Suspended => RegSt::Suspended, RegSt::Revoked => RegSt::Revoked }
}

#[derive(Clone, Copy, Debug, PartialEq)]
struct Msg { st: u8, ver: u64, orig: u64 } // st: 0 Absent 1 Enrolled 2 Suspended 3 Revoked
fn code(s: &RegSt) -> u8 { match s { RegSt::Absent => 0, RegSt::Enrolled => 1, RegSt::Suspended => 2, RegSt::Revoked => 3 } }
fn decode(c: u8) -> RegSt { match c { 0 => RegSt::Absent, 1 => RegSt::Enrolled, 2 => RegSt::Suspended, _ => RegSt::Revoked } }

/// One device (d1) of the model's state.
struct S {
    reg: RegSt, reg_ver: u64, dev: DevSt, pdp_st: RegSt, pdp_ver: u64, pdp_age: u64, pdp_orig: u64,
    since_rev: u64, now: u64, use_cnt: u64, bad_grants: u64, link: Link, net: Vec<Msg>, active_ev: bool,
}

#[derive(Clone, Copy)]
enum A { Enroll, Suspend, Revoke, Push(u64), Deliver(Msg), Poll, Sync, Observe, Access, Tick, Partition }

fn init() -> S {
    S { reg: RegSt::Absent, reg_ver: 0, dev: DevSt::Unprov, pdp_st: RegSt::Absent, pdp_ver: 0, pdp_age: 0,
        pdp_orig: 0, since_rev: 0, now: 0, use_cnt: 0, bad_grants: 0, link: Link::Up, net: vec![], active_ev: false }
}

fn consts() -> RuleConsts { RuleConsts { lease: LEASE, skewbound: SKEWBOUND, maxuse: MAXUSE } }

fn inputs(s: &S) -> RuleInputs {
    RuleInputs {
        dev: match s.dev { DevSt::Unprov => DevSt::Unprov, DevSt::Prov => DevSt::Prov, DevSt::Inv => DevSt::Inv },
        reg: copy(&s.reg), pdp_st: copy(&s.pdp_st), pdp_age: s.pdp_age, pdp_orig: s.pdp_orig,
        use_cnt: s.use_cnt, now: s.now,
        link: match s.link { Link::Up => Link::Up, Link::Down => Link::Down },
        critical_active: s.active_ev, // EVENTTYPES = CRITICAL = {e1}
    }
}

fn allow(rule: &Rule, s: &S) -> bool { exec_allow_rule(rule, &inputs(s), &consts()) }

fn reg_change(s: &mut S, to: RegSt) {
    assert!(s.reg_ver < MAXVER, "RegChange: regVer < MAXVER");
    let ok = match (&s.reg, &to) {
        (RegSt::Absent, RegSt::Enrolled) => true,
        (RegSt::Enrolled, RegSt::Suspended | RegSt::Revoked) => true,
        (RegSt::Suspended, RegSt::Enrolled | RegSt::Revoked) => true,
        _ => false,
    };
    assert!(ok, "RegTransition");
    if eq(&to, &RegSt::Revoked) { s.since_rev = 0; }
    s.reg = to;
    s.reg_ver += 1;
}

fn apply(rule: &Rule, s: &mut S, a: A) {
    match a {
        A::Enroll => reg_change(s, RegSt::Enrolled),
        A::Suspend => reg_change(s, RegSt::Suspended),
        A::Revoke => reg_change(s, RegSt::Revoked),
        A::Push(t) => {
            assert!(matches!(s.link, Link::Up) && s.net.len() < MAXNET && t <= MAXT);
            assert!((t as i64 - s.now as i64) <= SKEW && (s.now as i64 - t as i64) <= SKEW);
            let m = Msg { st: code(&s.reg), ver: s.reg_ver, orig: t };
            if !s.net.contains(&m) { s.net.push(m); }
        }
        A::Deliver(m) => {
            let i = s.net.iter().position(|x| *x == m).expect("DeliverNotify: m \\in net");
            s.net.remove(i);
            if m.ver > s.pdp_ver {
                s.pdp_st = decode(m.st); s.pdp_ver = m.ver; s.pdp_age = 0; s.pdp_orig = m.orig; s.use_cnt = 0;
            }
        }
        A::Poll => {
            assert!(matches!(s.link, Link::Up), "PdpPoll: link Up");
            s.pdp_st = copy(&s.reg); s.pdp_ver = s.reg_ver; s.pdp_age = 0; s.pdp_orig = s.now; s.use_cnt = 0;
        }
        A::Sync => {
            s.dev = match s.reg { RegSt::Enrolled => DevSt::Prov, RegSt::Revoked | RegSt::Suspended => DevSt::Inv, RegSt::Absent => DevSt::Unprov };
        }
        A::Observe => { assert!(!s.active_ev, "ObserveEvent: e \\notin activeEv"); s.active_ev = true; }
        A::Access => {
            assert!(allow(rule, s), "RecordAccess: AllowRule(d)");
            s.use_cnt = if s.use_cnt + 1 > MAXUSE { MAXUSE } else { s.use_cnt + 1 };
            if !(eq(&s.reg, &RegSt::Enrolled) || s.bad_grants == MAXBAD) { s.bad_grants += 1; }
        }
        A::Tick => {
            assert!(s.now < MAXT, "Tick: now < MAXT");
            s.now += 1;
            s.pdp_age = if s.pdp_age + 1 > MAXAGE { MAXAGE } else { s.pdp_age + 1 };
            if eq(&s.reg, &RegSt::Revoked) { s.since_rev = if s.since_rev + 1 > MAXAGE { MAXAGE } else { s.since_rev + 1 }; }
        }
        A::Partition => { assert!(matches!(s.link, Link::Up)); s.link = Link::Down; }
    }
}

fn run(rule: &Rule, trace: &[A]) -> S {
    let mut s = init();
    for a in trace { apply(rule, &mut s, *a); }
    s
}

/// Does the final state violate the property (for device d1)?
fn violates(prop: &str, rule: &Rule, s: &S) -> bool {
    let g = allow(rule, s);
    let enrolled = eq(&s.reg, &RegSt::Enrolled);
    match prop {
        "S1" => g && !enrolled,
        "S2" => eq(&s.reg, &RegSt::Revoked) && g,
        "S3" => eq(&s.reg, &RegSt::Revoked) && s.since_rev > LEASE && g,
        "S5" => s.active_ev && g,
        "S6" => eq(&s.reg, &RegSt::Suspended) && g,
        "S7" => !(s.bad_grants < MAXBAD),
        "AV" => matches!(s.link, Link::Up) && enrolled && !s.active_ev && !g,
        "AVP" => enrolled && !s.active_ev && !g,
        "AVPD" => enrolled && !s.active_ev && s.pdp_ver == s.reg_ver
            && (s.now as i64 - s.pdp_orig as i64) <= (LEASE - SKEWBOUND) as i64 && !g,
        _ => unreachable!(),
    }
}

const M1: Msg = Msg { st: 1, ver: 1, orig: 0 };

fn traces(name: &str) -> Vec<A> {
    use A::*;
    match name {
        "T1" => vec![Enroll, Sync, Revoke, Tick, Tick],
        "T2" => vec![Enroll, Poll, Revoke, Tick, Tick],
        "T3" => vec![Enroll, Push(0), Revoke, Tick, Tick, Deliver(M1)],
        "T4" => vec![Enroll, Sync, Observe],
        "T5" => vec![Enroll, Poll, Observe],
        "T6" => vec![Enroll, Observe],
        "T7" => vec![Enroll, Poll],
        "T8" => vec![Enroll, Poll, Partition],
        "T9" => vec![Enroll, Poll, Access],
        "T10" => vec![Enroll, Poll, Revoke],
        "T11" => vec![Enroll, Poll, Suspend],
        "T12" => vec![Enroll, Sync, Suspend],
        "T13a" => vec![Enroll, Sync, Revoke, Access, Access, Access],
        "T13" => vec![Enroll, Poll, Revoke, Access, Access, Access],
        "T14" => vec![Enroll],
        "T15" => vec![Enroll, Partition],
        _ => unreachable!(),
    }
}

/// (rule, property, trace) for every ✗ cell of the paper's table, as in src/rules_cex.rs.
fn cells() -> Vec<(Rule, &'static str, &'static str)> {
    use Rule::*;
    let mut v = vec![
        (A1, "S1", "T1"), (A1, "S2", "T1"), (A1, "S3", "T1"), (A1, "S5", "T4"), (A1, "S6", "T12"),
        (A1, "S7", "T13a"), (A1, "AV", "T14"), (A1, "AVP", "T14"), (A1, "AVPD", "T7"),
        (A2, "S3", "T2"), (A2, "S5", "T5"),
        (A3, "S3", "T3"), (A3, "S5", "T5"),
        (A4, "S5", "T6"), (A4, "AVP", "T15"), (A4, "AVPD", "T8"),
        (A5, "S3", "T3"),
        (A6, "AVP", "T15"), (A6, "AVPD", "T8"),
        (A7, "S3", "T2"), (A7, "AVPD", "T9"),
    ];
    for r in [A2, A3, A5, A7, A8] {
        let r2 = |r: &Rule| match r { A2 => A2, A3 => A3, A5 => A5, A7 => A7, _ => A8 };
        v.push((r2(&r), "S1", "T10"));
        v.push((r2(&r), "S2", "T10"));
        v.push((r2(&r), "S6", "T11"));
        v.push((r2(&r), "AV", "T14"));
        v.push((r2(&r), "AVP", "T14"));
    }
    for r in [A2, A3, A5, A8] {
        let r2 = match r { A2 => A2, A3 => A3, A5 => A5, _ => A8 };
        v.push((r2, "S7", "T13"));
    }
    v
}

#[test]
fn all_50_counterexamples_replay_and_violate() {
    let cs = cells();
    assert_eq!(cs.len(), 50, "the paper's table has 50 ✗ cells");
    for (rule, prop, t) in &cs {
        let s = run(rule, &traces(t));
        assert!(violates(prop, rule, &s), "{t} does not violate {prop} under rule");
    }
}

/// Non-vacuity of the test harness: the same traces do NOT violate the
/// property under a rule for which the paper (and src/rules_proofs.rs) says ✓.
#[test]
fn check_mark_rules_are_not_violated_by_these_traces() {
    // S3 for A8 on the delayed-notification trace (A3's counterexample)
    let s = run(&Rule::A8, &traces("T3"));
    assert!(!violates("S3", &Rule::A8, &s));
    // S5 for A5..A8 on T5
    for r in [Rule::A5, Rule::A6, Rule::A7, Rule::A8] {
        let s = run(&r, &traces("T5"));
        assert!(!violates("S5", &r, &s));
    }
    // AVPD for A2, A3, A5, A8 on T7
    for r in [Rule::A2, Rule::A3, Rule::A5, Rule::A8] {
        let s = run(&r, &traces("T7"));
        assert!(!violates("AVPD", &r, &s));
    }
}
