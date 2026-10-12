//! Extension A: the ✗ cells. Each is a concrete execution in the paper's
//! configuration (paper_params) that Verus checks step by step against
//! system_spec.rs (`is_execution`: Init, then every action in range, enabled,
//! and producing exactly the next state), and whose last state violates the
//! property. The same traces are replayed as Rust tests in
//! tests/rules_counterexamples.rs.
use vstd::prelude::*;
use crate::system_spec::*;
use crate::rules_spec::*;

verus! {

pub open spec fn init_state(p: Params) -> State {
    State {
        reg: Seq::new(p.ndev, |d: int| RegSt::Absent),
        reg_ver: Seq::new(p.ndev, |d: int| 0nat),
        dev: Seq::new(p.ndev, |d: int| DevSt::Unprov),
        pdp_st: Seq::new(p.ndev, |d: int| RegSt::Absent),
        pdp_ver: Seq::new(p.ndev, |d: int| 0nat),
        pdp_age: Seq::new(p.ndev, |d: int| 0nat),
        pdp_orig: Seq::new(p.ndev, |d: int| 0nat),
        since_rev: Seq::new(p.ndev, |d: int| 0nat),
        now: 0,
        use_cnt: Seq::new(p.ndev, |d: int| 0nat),
        bad_grants: Seq::new(p.ndev, |d: int| 0nat),
        link: Link::Up,
        net: Set::<Msg>::empty(),
        active_ev: Seq::new(p.ndev, |d: int| Set::<nat>::empty()),
    }
}

/// A violating execution establishes a ✗ cell.
pub proof fn lemma_violated_by(p: Params, rule: Rule, prop: Prop, ss: Seq<State>, acts: Seq<Action>)
    requires
        is_execution(p, rule, ss, acts),
        !prop_holds(p, rule, prop, ss.last()),
    ensures
        cell_violated(p, rule, prop),
{
    assert(reachable(p, rule, ss.last()));
}

// Actions used below (device 0 = d1, event 0 = e1).
pub open spec fn enroll() -> Action { Action::RegChange { d: 0, to: RegSt::Enrolled } }
pub open spec fn revoke() -> Action { Action::RegChange { d: 0, to: RegSt::Revoked } }
pub open spec fn sync() -> Action { Action::SyncFromRegistry { d: 0 } }
pub open spec fn poll() -> Action { Action::PdpPoll { d: 0 } }
pub open spec fn observe() -> Action { Action::ObserveEvent { d: 0, e: 0 } }
pub open spec fn enrolled_msg() -> Msg { Msg { dv: 0, st: RegSt::Enrolled, ver: 1, orig: 0 } }

// ---------------------------------------------------------------------------
// Trace T1: Enroll; SyncFromRegistry; Revoke; Tick; Tick
//   dev[d1] = "Prov" is never refreshed; sinceRev = 2 > LEASE = 1.
// ---------------------------------------------------------------------------
pub proof fn lemma_trace_t1(rule: Rule) -> (r: (Seq<State>, Seq<Action>))
    ensures
        is_execution(paper_params(), rule, r.0, r.1),
        r.0.last().reg[0] == RegSt::Revoked,
        r.0.last().since_rev[0] == 2,
        r.0.last().dev[0] == DevSt::Prov,
{
    let p = paper_params();
    let a = seq![enroll(), sync(), revoke(), Action::Tick, Action::Tick];
    let s0 = init_state(p);
    let s1 = effect(p, s0, a[0]);
    let s2 = effect(p, s1, a[1]);
    let s3 = effect(p, s2, a[2]);
    let s4 = effect(p, s3, a[3]);
    let s5 = effect(p, s4, a[4]);
    let ss = seq![s0, s1, s2, s3, s4, s5];
    assert(step(p, rule, s0, a[0], s1));
    assert(step(p, rule, s1, a[1], s2));
    assert(step(p, rule, s2, a[2], s3));
    assert(step(p, rule, s3, a[3], s4));
    assert(step(p, rule, s4, a[4], s5));
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] step(p, rule, ss[i], a[i], ss[i + 1]) by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else {}
    }
    (ss, a)
}

// ---------------------------------------------------------------------------
// Trace T2: Enroll; PdpPoll; Revoke; Tick; Tick
//   the decision point caches "Enrolled" (ver 1) and is never told of the revocation.
// ---------------------------------------------------------------------------
pub proof fn lemma_trace_t2(rule: Rule) -> (r: (Seq<State>, Seq<Action>))
    ensures
        is_execution(paper_params(), rule, r.0, r.1),
        r.0.last().reg[0] == RegSt::Revoked,
        r.0.last().since_rev[0] == 2,
        r.0.last().pdp_st[0] == RegSt::Enrolled,
        r.0.last().pdp_age[0] == 2,
        r.0.last().use_cnt[0] == 0,
        r.0.last().active_ev[0] == Set::<nat>::empty(),
{
    let p = paper_params();
    let a = seq![enroll(), poll(), revoke(), Action::Tick, Action::Tick];
    let s0 = init_state(p);
    let s1 = effect(p, s0, a[0]);
    let s2 = effect(p, s1, a[1]);
    let s3 = effect(p, s2, a[2]);
    let s4 = effect(p, s3, a[3]);
    let s5 = effect(p, s4, a[4]);
    let ss = seq![s0, s1, s2, s3, s4, s5];
    assert(step(p, rule, s0, a[0], s1));
    assert(step(p, rule, s1, a[1], s2));
    assert(step(p, rule, s2, a[2], s3));
    assert(step(p, rule, s3, a[3], s4));
    assert(step(p, rule, s4, a[4], s5));
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] step(p, rule, ss[i], a[i], ss[i + 1]) by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else {}
    }
    (ss, a)
}

// ---------------------------------------------------------------------------
// Trace T3 (the paper's A3 finding): Enroll; PushNotify(t = 0); Revoke; Tick; Tick;
//   DeliverNotify(<<d1, Enrolled, ver 1, orig 0>>)
//   a version-ordered but delayed notification is accepted (1 > 0) and resets pdpAge.
// ---------------------------------------------------------------------------
pub proof fn lemma_trace_t3(rule: Rule) -> (r: (Seq<State>, Seq<Action>))
    ensures
        is_execution(paper_params(), rule, r.0, r.1),
        r.0.last().reg[0] == RegSt::Revoked,
        r.0.last().since_rev[0] == 2,
        r.0.last().pdp_st[0] == RegSt::Enrolled,
        r.0.last().pdp_age[0] == 0,
        r.0.last().active_ev[0] == Set::<nat>::empty(),
{
    let p = paper_params();
    let a = seq![enroll(), Action::PushNotify { d: 0, t: 0 }, revoke(), Action::Tick, Action::Tick,
                 Action::DeliverNotify { m: enrolled_msg() }];
    let s0 = init_state(p);
    let s1 = effect(p, s0, a[0]);
    let s2 = effect(p, s1, a[1]);
    let s3 = effect(p, s2, a[2]);
    let s4 = effect(p, s3, a[3]);
    let s5 = effect(p, s4, a[4]);
    let s6 = effect(p, s5, a[5]);
    let ss = seq![s0, s1, s2, s3, s4, s5, s6];
    assert(s2.net == set![enrolled_msg()]);
    assert(s2.net.len() == 1);
    assert(step(p, rule, s0, a[0], s1));
    assert(step(p, rule, s1, a[1], s2));
    assert(step(p, rule, s2, a[2], s3));
    assert(step(p, rule, s3, a[3], s4));
    assert(step(p, rule, s4, a[4], s5));
    assert(s5.net.contains(enrolled_msg()));
    assert(step(p, rule, s5, a[5], s6));
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] step(p, rule, ss[i], a[i], ss[i + 1]) by {
        if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} else {}
    }
    (ss, a)
}

// ---------------------------------------------------------------------------
// Trace T4: Enroll; SyncFromRegistry; ObserveEvent(e1)      (A1 grants under a critical event)
// Trace T5: Enroll; PdpPoll; ObserveEvent(e1)               (A2, A3)
// Trace T6: Enroll; ObserveEvent(e1)                        (A4)
// ---------------------------------------------------------------------------
pub proof fn lemma_trace_3steps(rule: Rule, a0: Action, a1: Action, a2: Action) -> (r: (Seq<State>, Seq<Action>))
    requires
        a0 == enroll(),
        (a1 == sync() || a1 == poll()),
        a2 == observe(),
    ensures
        is_execution(paper_params(), rule, r.0, r.1),
        r.0.last() == effect(paper_params(), effect(paper_params(), effect(paper_params(), init_state(paper_params()), a0), a1), a2),
{
    let p = paper_params();
    let a = seq![a0, a1, a2];
    let s0 = init_state(p);
    let s1 = effect(p, s0, a[0]);
    let s2 = effect(p, s1, a[1]);
    let s3 = effect(p, s2, a[2]);
    let ss = seq![s0, s1, s2, s3];
    assert(step(p, rule, s0, a[0], s1));
    assert(step(p, rule, s1, a[1], s2));
    assert(step(p, rule, s2, a[2], s3));
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] step(p, rule, ss[i], a[i], ss[i + 1]) by {
        if i == 0 {} else if i == 1 {} else {}
    }
    (ss, a)
}

pub proof fn lemma_trace_t6(rule: Rule) -> (r: (Seq<State>, Seq<Action>))
    ensures
        is_execution(paper_params(), rule, r.0, r.1),
        r.0.last().reg[0] == RegSt::Enrolled,
        r.0.last().link == Link::Up,
        r.0.last().active_ev[0] == set![0nat],
{
    let p = paper_params();
    let a = seq![enroll(), observe()];
    let s0 = init_state(p);
    let s1 = effect(p, s0, a[0]);
    let s2 = effect(p, s1, a[1]);
    let ss = seq![s0, s1, s2];
    assert(step(p, rule, s0, a[0], s1));
    assert(step(p, rule, s1, a[1], s2));
    assert(s2.active_ev[0] =~= set![0nat]);
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] step(p, rule, ss[i], a[i], ss[i + 1]) by {
        if i == 0 {} else {}
    }
    (ss, a)
}

// ---------------------------------------------------------------------------
// Trace T7: Enroll; PdpPoll           (fresh, current cache; AVPD's premise holds)
// Trace T8: Enroll; PdpPoll; Partition
// Trace T9: Enroll; PdpPoll; RecordAccess(d1)   (A7 spends its one grant)
// ---------------------------------------------------------------------------
pub proof fn lemma_trace_t7(rule: Rule, extra: Seq<Action>) -> (r: (Seq<State>, Seq<Action>))
    requires
        extra.len() == 0 || extra == seq![Action::Partition]
            || (extra == seq![Action::RecordAccess { d: 0 }] && rule == Rule::A7),
    ensures
        is_execution(paper_params(), rule, r.0, r.1),
        r.0.last().reg[0] == RegSt::Enrolled,
        r.0.last().pdp_ver[0] == r.0.last().reg_ver[0],
        r.0.last().pdp_st[0] == RegSt::Enrolled,
        r.0.last().now == 0,
        r.0.last().pdp_orig[0] == 0,
        r.0.last().dev[0] == DevSt::Unprov,
        r.0.last().active_ev[0] == Set::<nat>::empty(),
        extra.len() == 0 ==> r.0.last().link == Link::Up,
        extra == seq![Action::Partition] ==> r.0.last().link == Link::Down,
        extra == seq![Action::RecordAccess { d: 0 }] ==> r.0.last().use_cnt[0] == 1,
{
    let p = paper_params();
    let s0 = init_state(p);
    let s1 = effect(p, s0, enroll());
    let s2 = effect(p, s1, poll());
    assert(step(p, rule, s0, enroll(), s1));
    assert(step(p, rule, s1, poll(), s2));
    assert(s2.active_ev[0] == Set::<nat>::empty());
    assert(Set::<nat>::empty().intersect(p.critical) =~= Set::<nat>::empty());
    if extra.len() == 0 {
        let a = seq![enroll(), poll()];
        let ss = seq![s0, s1, s2];
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] step(p, rule, ss[i], a[i], ss[i + 1]) by {
            if i == 0 {} else {}
        }
        (ss, a)
    } else {
        let x = extra[0];
        let s3 = effect(p, s2, x);
        if x == Action::Partition {
            assert(step(p, rule, s2, x, s3));
        } else {
            assert(a7_count_lease(p, s2, 0));
            assert(step(p, rule, s2, x, s3));
        }
        let a = seq![enroll(), poll(), x];
        let ss = seq![s0, s1, s2, s3];
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] step(p, rule, ss[i], a[i], ss[i + 1]) by {
            if i == 0 {} else if i == 1 {} else {}
        }
        (ss, a)
    }
}

// ---------------------------------------------------------------------------
// The 13 ✗ cells among S3, S5, AVPD
// ---------------------------------------------------------------------------

proof fn lemma_empty_no_critical(p: Params)
    ensures
        Set::<nat>::empty().intersect(p.critical) == Set::<nat>::empty(),
{
    assert(Set::<nat>::empty().intersect(p.critical) =~= Set::<nat>::empty());
}

/// S3 ✗ for A1 (trace T1)
pub proof fn lemma_cell_s3_a1_violated() ensures cell_violated(paper_params(), Rule::A1, Prop::S3) {
    let (ss, a) = lemma_trace_t1(Rule::A1);
    assert(allow_rule(paper_params(), Rule::A1, ss.last(), 0));
    lemma_violated_by(paper_params(), Rule::A1, Prop::S3, ss, a);
}

/// S3 ✗ for A2 (trace T2)
pub proof fn lemma_cell_s3_a2_violated() ensures cell_violated(paper_params(), Rule::A2, Prop::S3) {
    let (ss, a) = lemma_trace_t2(Rule::A2);
    assert(allow_rule(paper_params(), Rule::A2, ss.last(), 0));
    lemma_violated_by(paper_params(), Rule::A2, Prop::S3, ss, a);
}

/// S3 ✗ for A3 (trace T3, the delayed notification)
pub proof fn lemma_cell_s3_a3_violated() ensures cell_violated(paper_params(), Rule::A3, Prop::S3) {
    let (ss, a) = lemma_trace_t3(Rule::A3);
    assert(allow_rule(paper_params(), Rule::A3, ss.last(), 0));
    lemma_violated_by(paper_params(), Rule::A3, Prop::S3, ss, a);
}

/// S3 ✗ for A5 (trace T3; no event is active)
pub proof fn lemma_cell_s3_a5_violated() ensures cell_violated(paper_params(), Rule::A5, Prop::S3) {
    let (ss, a) = lemma_trace_t3(Rule::A5);
    lemma_empty_no_critical(paper_params());
    assert(allow_rule(paper_params(), Rule::A5, ss.last(), 0));
    lemma_violated_by(paper_params(), Rule::A5, Prop::S3, ss, a);
}

/// S3 ✗ for A7 (trace T2; no grant spent, useCnt = 0 < MAXUSE = 1)
pub proof fn lemma_cell_s3_a7_violated() ensures cell_violated(paper_params(), Rule::A7, Prop::S3) {
    let (ss, a) = lemma_trace_t2(Rule::A7);
    lemma_empty_no_critical(paper_params());
    assert(allow_rule(paper_params(), Rule::A7, ss.last(), 0));
    lemma_violated_by(paper_params(), Rule::A7, Prop::S3, ss, a);
}

proof fn lemma_critical_active(s: State)
    requires
        s.active_ev[0] == set![0nat],
    ensures
        s.active_ev[0].intersect(paper_params().critical) != Set::<nat>::empty(),
{
    assert(s.active_ev[0].intersect(paper_params().critical).contains(0));
}

/// S5 ✗ for A1 (trace T4)
pub proof fn lemma_cell_s5_a1_violated() ensures cell_violated(paper_params(), Rule::A1, Prop::S5) {
    let p = paper_params();
    let (ss, a) = lemma_trace_3steps(Rule::A1, enroll(), sync(), observe());
    let s = ss.last();
    assert(s.active_ev[0] =~= set![0nat]);
    lemma_critical_active(s);
    assert(allow_rule(p, Rule::A1, s, 0));
    lemma_violated_by(p, Rule::A1, Prop::S5, ss, a);
}

/// S5 ✗ for A2 (trace T5)
pub proof fn lemma_cell_s5_a2_violated() ensures cell_violated(paper_params(), Rule::A2, Prop::S5) {
    let p = paper_params();
    let (ss, a) = lemma_trace_3steps(Rule::A2, enroll(), poll(), observe());
    let s = ss.last();
    assert(s.active_ev[0] =~= set![0nat]);
    lemma_critical_active(s);
    assert(allow_rule(p, Rule::A2, s, 0));
    lemma_violated_by(p, Rule::A2, Prop::S5, ss, a);
}

/// S5 ✗ for A3 (trace T5)
pub proof fn lemma_cell_s5_a3_violated() ensures cell_violated(paper_params(), Rule::A3, Prop::S5) {
    let p = paper_params();
    let (ss, a) = lemma_trace_3steps(Rule::A3, enroll(), poll(), observe());
    let s = ss.last();
    assert(s.active_ev[0] =~= set![0nat]);
    lemma_critical_active(s);
    assert(allow_rule(p, Rule::A3, s, 0));
    lemma_violated_by(p, Rule::A3, Prop::S5, ss, a);
}

/// S5 ✗ for A4 (trace T6)
pub proof fn lemma_cell_s5_a4_violated() ensures cell_violated(paper_params(), Rule::A4, Prop::S5) {
    let p = paper_params();
    let (ss, a) = lemma_trace_t6(Rule::A4);
    lemma_critical_active(ss.last());
    assert(allow_rule(p, Rule::A4, ss.last(), 0));
    lemma_violated_by(p, Rule::A4, Prop::S5, ss, a);
}

/// AVPD ✗ for A1 (trace T7: dev[d1] still "Unprov")
pub proof fn lemma_cell_avpd_a1_violated() ensures cell_violated(paper_params(), Rule::A1, Prop::AVPD) {
    let p = paper_params();
    let (ss, a) = lemma_trace_t7(Rule::A1, Seq::empty());
    lemma_empty_no_critical(p);
    assert(!allow_rule(p, Rule::A1, ss.last(), 0));
    assert(no_critical(p, ss.last(), 0));
    lemma_violated_by(p, Rule::A1, Prop::AVPD, ss, a);
}

/// AVPD ✗ for A4 (trace T8: partitioned)
pub proof fn lemma_cell_avpd_a4_violated() ensures cell_violated(paper_params(), Rule::A4, Prop::AVPD) {
    let p = paper_params();
    let (ss, a) = lemma_trace_t7(Rule::A4, seq![Action::Partition]);
    lemma_empty_no_critical(p);
    assert(!allow_rule(p, Rule::A4, ss.last(), 0));
    assert(no_critical(p, ss.last(), 0));
    lemma_violated_by(p, Rule::A4, Prop::AVPD, ss, a);
}

/// AVPD ✗ for A6 (trace T8: partitioned)
pub proof fn lemma_cell_avpd_a6_violated() ensures cell_violated(paper_params(), Rule::A6, Prop::AVPD) {
    let p = paper_params();
    let (ss, a) = lemma_trace_t7(Rule::A6, seq![Action::Partition]);
    lemma_empty_no_critical(p);
    assert(!allow_rule(p, Rule::A6, ss.last(), 0));
    assert(no_critical(p, ss.last(), 0));
    lemma_violated_by(p, Rule::A6, Prop::AVPD, ss, a);
}

/// AVPD ✗ for A7 (trace T9: the grant budget is spent; the cache is still fresh and current)
pub proof fn lemma_cell_avpd_a7_violated() ensures cell_violated(paper_params(), Rule::A7, Prop::AVPD) {
    let p = paper_params();
    let (ss, a) = lemma_trace_t7(Rule::A7, seq![Action::RecordAccess { d: 0 }]);
    lemma_empty_no_critical(p);
    assert(!allow_rule(p, Rule::A7, ss.last(), 0));
    assert(no_critical(p, ss.last(), 0));
    lemma_violated_by(p, Rule::A7, Prop::AVPD, ss, a);
}

} // verus!

verus! {

pub open spec fn suspend() -> Action { Action::RegChange { d: 0, to: RegSt::Suspended } }
pub open spec fn access() -> Action { Action::RecordAccess { d: 0 } }

// ---------------------------------------------------------------------------
// Trace T10: Enroll; PdpPoll; Revoke     (cache "Enrolled", fresh; registry Revoked)
// Trace T11: Enroll; PdpPoll; Suspend    (cache "Enrolled", fresh; registry Suspended)
// Trace T12: Enroll; SyncFromRegistry; Suspend   (dev "Prov"; registry Suspended)
// ---------------------------------------------------------------------------
pub proof fn lemma_trace_change(rule: Rule, view: Action, change: Action) -> (r: (Seq<State>, Seq<Action>))
    requires
        view == poll() || view == sync(),
        change == revoke() || change == suspend(),
    ensures
        is_execution(paper_params(), rule, r.0, r.1),
        r.1 == seq![enroll(), view, change],
        r.0.len() == 4,
        r.0.last() == effect(paper_params(), effect(paper_params(), effect(paper_params(), init_state(paper_params()), enroll()), view), change),
{
    let p = paper_params();
    let a = seq![enroll(), view, change];
    let s0 = init_state(p);
    let s1 = effect(p, s0, a[0]);
    let s2 = effect(p, s1, a[1]);
    let s3 = effect(p, s2, a[2]);
    let ss = seq![s0, s1, s2, s3];
    assert(step(p, rule, s0, a[0], s1));
    assert(step(p, rule, s1, a[1], s2));
    assert(step(p, rule, s2, a[2], s3));
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] step(p, rule, ss[i], a[i], ss[i + 1]) by {
        if i == 0 {} else if i == 1 {} else {}
    }
    (ss, a)
}

// ---------------------------------------------------------------------------
// Trace T13: Enroll; <SyncFromRegistry for A1, PdpPoll otherwise>; Revoke; RecordAccess x3
//   three grants while revoked: badGrants = 3 = MAXBAD.
// ---------------------------------------------------------------------------
/// One RecordAccess while revoked: a grant (the rule allows) that adds one bad grant.
/// A1, A2, A3, A5, A8 do not read useCnt, so they still allow afterwards.
pub proof fn lemma_access_step(rule: Rule, s: State) -> (s2: State)
    requires
        rule == Rule::A1 || rule == Rule::A2 || rule == Rule::A3 || rule == Rule::A5 || rule == Rule::A8,
        state_shape(paper_params(), s),
        allow_rule(paper_params(), rule, s, 0),
        s.reg[0] == RegSt::Revoked,
        s.bad_grants[0] < 3,
    ensures
        step(paper_params(), rule, s, access(), s2),
        s2 == effect(paper_params(), s, access()),
        state_shape(paper_params(), s2),
        allow_rule(paper_params(), rule, s2, 0),
        s2.reg[0] == RegSt::Revoked,
        s2.bad_grants[0] == s.bad_grants[0] + 1,
{
    let p = paper_params();
    let s2 = effect(p, s, access());
    assert(s2.dev == s.dev && s2.pdp_st == s.pdp_st && s2.pdp_age == s.pdp_age && s2.pdp_orig == s.pdp_orig
        && s2.now == s.now && s2.active_ev == s.active_ev && s2.reg == s.reg && s2.link == s.link);
    assert(step(p, rule, s, access(), s2));
    s2
}

pub proof fn lemma_trace_damage(rule: Rule) -> (r: (Seq<State>, Seq<Action>))
    requires
        rule == Rule::A1 || rule == Rule::A2 || rule == Rule::A3 || rule == Rule::A5 || rule == Rule::A8,
    ensures
        is_execution(paper_params(), rule, r.0, r.1),
        r.0.last().bad_grants[0] == 3,
{
    let p = paper_params();
    let view = if rule == Rule::A1 { sync() } else { poll() };
    let (ss3, a3) = lemma_trace_change(rule, view, revoke());
    let s3 = ss3.last();
    assert(Set::<nat>::empty().intersect(p.critical) =~= Set::<nat>::empty());
    assert(s3.bad_grants[0] == 0 && s3.reg[0] == RegSt::Revoked);
    assert(allow_rule(p, rule, s3, 0));
    let s4 = lemma_access_step(rule, s3);
    let s5 = lemma_access_step(rule, s4);
    let s6 = lemma_access_step(rule, s5);
    let a = a3 + seq![access(), access(), access()];
    let ss = ss3 + seq![s4, s5, s6];
    assert forall|i: int| 0 <= i < a.len() implies #[trigger] step(p, rule, ss[i], a[i], ss[i + 1]) by {
        if i < 3 {
            assert(ss[i] == ss3[i] && ss[i + 1] == ss3[i + 1] && a[i] == a3[i]);
        } else if i == 3 {
            assert(ss[i] == s3 && ss[i + 1] == s4 && a[i] == access());
        } else if i == 4 {
            assert(ss[i] == s4 && ss[i + 1] == s5 && a[i] == access());
        } else {
            assert(ss[i] == s5 && ss[i + 1] == s6 && a[i] == access());
        }
    }
    assert(ss[0] == ss3[0]);
    (ss, a)
}

// ---------------------------------------------------------------------------
// Trace T14: Enroll                   (enrolled, link up, no event; nothing cached yet)
// Trace T15: Enroll; Partition
// ---------------------------------------------------------------------------
pub proof fn lemma_trace_enroll(rule: Rule, partition: bool) -> (r: (Seq<State>, Seq<Action>))
    ensures
        is_execution(paper_params(), rule, r.0, r.1),
        r.0.last().reg[0] == RegSt::Enrolled,
        r.0.last().pdp_st[0] == RegSt::Absent,
        r.0.last().dev[0] == DevSt::Unprov,
        r.0.last().active_ev[0] == Set::<nat>::empty(),
        r.0.last().link == (if partition { Link::Down } else { Link::Up }),
{
    let p = paper_params();
    let s0 = init_state(p);
    let s1 = effect(p, s0, enroll());
    assert(step(p, rule, s0, enroll(), s1));
    if partition {
        let s2 = effect(p, s1, Action::Partition);
        assert(step(p, rule, s1, Action::Partition, s2));
        let a = seq![enroll(), Action::Partition];
        let ss = seq![s0, s1, s2];
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] step(p, rule, ss[i], a[i], ss[i + 1]) by {
            if i == 0 {} else {}
        }
        (ss, a)
    } else {
        let a = seq![enroll()];
        let ss = seq![s0, s1];
        assert forall|i: int| 0 <= i < a.len() implies #[trigger] step(p, rule, ss[i], a[i], ss[i + 1]) by {}
        (ss, a)
    }
}

// ---------------------------------------------------------------------------
// The remaining 37 ✗ cells
// ---------------------------------------------------------------------------

/// S1 and S2 ✗ for A1 (trace T1: dev "Prov", registry Revoked)
pub proof fn lemma_cell_s1_a1_violated() ensures cell_violated(paper_params(), Rule::A1, Prop::S1) {
    let (ss, a) = lemma_trace_t1(Rule::A1);
    assert(allow_rule(paper_params(), Rule::A1, ss.last(), 0));
    lemma_violated_by(paper_params(), Rule::A1, Prop::S1, ss, a);
}
pub proof fn lemma_cell_s2_a1_violated() ensures cell_violated(paper_params(), Rule::A1, Prop::S2) {
    let (ss, a) = lemma_trace_t1(Rule::A1);
    assert(allow_rule(paper_params(), Rule::A1, ss.last(), 0));
    lemma_violated_by(paper_params(), Rule::A1, Prop::S2, ss, a);
}

/// S1, S2 (trace T10) and S6 (trace T11) ✗ for the cache rules A2, A3, A5, A7, A8:
/// the decision point still holds a fresh "Enrolled" after the registry changed.
pub proof fn lemma_cell_cache_rules_violated(rule: Rule, prop: Prop)
    requires
        rule == Rule::A2 || rule == Rule::A3 || rule == Rule::A5 || rule == Rule::A7 || rule == Rule::A8,
        prop == Prop::S1 || prop == Prop::S2 || prop == Prop::S6,
    ensures
        cell_violated(paper_params(), rule, prop),
{
    let p = paper_params();
    let change = if prop == Prop::S6 { suspend() } else { revoke() };
    let (ss, a) = lemma_trace_change(rule, poll(), change);
    assert(Set::<nat>::empty().intersect(p.critical) =~= Set::<nat>::empty());
    assert(allow_rule(p, rule, ss.last(), 0));
    lemma_violated_by(p, rule, prop, ss, a);
}

/// S6 ✗ for A1 (trace T12)
pub proof fn lemma_cell_s6_a1_violated() ensures cell_violated(paper_params(), Rule::A1, Prop::S6) {
    let (ss, a) = lemma_trace_change(Rule::A1, sync(), suspend());
    assert(allow_rule(paper_params(), Rule::A1, ss.last(), 0));
    lemma_violated_by(paper_params(), Rule::A1, Prop::S6, ss, a);
}

/// S7 ✗ for A1 (trace T13 with SyncFromRegistry)
pub proof fn lemma_cell_s7_a1_violated() ensures cell_violated(paper_params(), Rule::A1, Prop::S7) {
    let (ss, a) = lemma_trace_damage(Rule::A1);
    lemma_violated_by(paper_params(), Rule::A1, Prop::S7, ss, a);
}

/// S7 ✗ for A2, A3, A5, A8 (trace T13 with PdpPoll)
pub proof fn lemma_cell_s7_cache_violated(rule: Rule)
    requires
        rule == Rule::A2 || rule == Rule::A3 || rule == Rule::A5 || rule == Rule::A8,
    ensures
        cell_violated(paper_params(), rule, Prop::S7),
{
    let (ss, a) = lemma_trace_damage(rule);
    lemma_violated_by(paper_params(), rule, Prop::S7, ss, a);
}

/// AV and AVP ✗ for A1, A2, A3, A5, A7, A8 (trace T14: enrolled, nothing cached or synced yet)
pub proof fn lemma_cell_av_avp_violated(rule: Rule, prop: Prop)
    requires
        rule != Rule::A4 && rule != Rule::A6,
        prop == Prop::AV || prop == Prop::AVP,
    ensures
        cell_violated(paper_params(), rule, prop),
{
    let p = paper_params();
    let (ss, a) = lemma_trace_enroll(rule, false);
    assert(Set::<nat>::empty().intersect(p.critical) =~= Set::<nat>::empty());
    assert(no_critical(p, ss.last(), 0));
    assert(!allow_rule(p, rule, ss.last(), 0));
    lemma_violated_by(p, rule, prop, ss, a);
}

/// AVP ✗ for A4, A6 (trace T15: enrolled but partitioned)
pub proof fn lemma_cell_avp_failclosed_violated(rule: Rule)
    requires
        rule == Rule::A4 || rule == Rule::A6,
    ensures
        cell_violated(paper_params(), rule, Prop::AVP),
{
    let p = paper_params();
    let (ss, a) = lemma_trace_enroll(rule, true);
    assert(Set::<nat>::empty().intersect(p.critical) =~= Set::<nat>::empty());
    assert(no_critical(p, ss.last(), 0));
    assert(!allow_rule(p, rule, ss.last(), 0));
    lemma_violated_by(p, rule, Prop::AVP, ss, a);
}

} // verus!
