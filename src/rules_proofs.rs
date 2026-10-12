//! Extension A: proofs of the ✓ cells. One rule-independent inductive
//! invariant (`inv`) over the transition system of system_spec.rs, proved
//! for executions of any length; each ✓ cell follows from it.
//! The invariant's conjuncts are those of the model's IndInv (L631-644)
//! that the cells need, plus two clock facts (marked NEW).
use vstd::prelude::*;
use crate::spec::*;
use crate::system_spec::*;
use crate::rules_spec::*;

verus! {

// ---------------------------------------------------------------------------
// The invariant
// ---------------------------------------------------------------------------

/// LifecycleVersion(st, v) (L564-568)
pub open spec fn lifecycle_version(st: RegSt, v: nat) -> bool {
    &&& (st == RegSt::Absent <==> v == 0)
    &&& (st == RegSt::Enrolled ==> v >= 1)
    &&& (st == RegSt::Suspended ==> v >= 2)
    &&& (st == RegSt::Revoked ==> v >= 2)
}

/// Per-device conjuncts.
pub open spec fn dev_inv(p: Params, s: State, d: int) -> bool {
    // RegistryVersionConsistent (L570-571), CacheVersionConsistent (L574-575)
    &&& lifecycle_version(s.reg[d], s.reg_ver[d])
    &&& lifecycle_version(s.pdp_st[d], s.pdp_ver[d])
    // TypeOK: regVer[d] \in 0..MAXVER (L125)
    &&& s.reg_ver[d] <= p.maxver
    // NEW: a device whose registry entry is Absent has never been synced to "Prov"/"Inv"
    &&& (s.reg[d] == RegSt::Absent ==> s.dev[d] == DevSt::Unprov)
    // CacheNotAheadOfRegistry (L557-558)
    &&& s.pdp_ver[d] <= s.reg_ver[d]
    // CacheMatchesCurrentVersion (L588-589)
    &&& (s.pdp_ver[d] == s.reg_ver[d] ==> s.pdp_st[d] == s.reg[d])
    // ClockCoherence, first conjunct (L599)
    &&& s.pdp_orig[d] <= s.now + p.skew
    // NEW: origin stamps never exceed MAXT (they come from t \in 0..MAXT or from now <= MAXT)
    &&& s.pdp_orig[d] <= p.maxt
    // NEW: the cache's age is at most its origin age plus SKEW
    &&& s.pdp_age[d] as int <= s.now as int - s.pdp_orig[d] as int + p.skew as int
    // sinceRev saturates at MAXAGE (TypeOK, L131)
    &&& s.since_rev[d] <= p.maxage
    // OriginPrecedesRevocation (L626-629)
    &&& (s.pdp_st[d] == RegSt::Enrolled && s.reg[d] == RegSt::Revoked
            ==> s.now as int - s.pdp_orig[d] as int + p.skew as int >= s.since_rev[d] as int)
}

/// Per-message conjuncts.
pub open spec fn msg_inv(p: Params, s: State, m: Msg) -> bool {
    &&& m.dv < p.ndev
    // NotificationVersionConsistent (L578-579)
    &&& lifecycle_version(m.st, m.ver)
    // NotificationsWellFormed (L616-617)
    &&& m.ver <= s.reg_ver[m.dv as int]
    // NotificationMatchesCurrentVersion (L591-592)
    &&& (m.ver == s.reg_ver[m.dv as int] ==> m.st == s.reg[m.dv as int])
    // NotificationOriginBounded (L604-605)
    &&& m.orig <= s.now + p.skew
    &&& m.orig <= p.maxt
    // NotificationPrecedesRevocation (L611-614)
    &&& (m.st == RegSt::Enrolled && s.reg[m.dv as int] == RegSt::Revoked
            ==> s.now as int - m.orig as int + p.skew as int >= s.since_rev[m.dv as int] as int)
}

pub open spec fn inv(p: Params, s: State) -> bool {
    &&& state_shape(p, s)
    // MAXNET bound on the channel (TypeOK, L138)
    &&& s.net.len() <= p.maxnet
    &&& s.now <= p.maxt
    &&& forall|d: int| 0 <= d < p.ndev ==> #[trigger] dev_inv(p, s, d)
    &&& forall|m: Msg| s.net.contains(m) ==> #[trigger] msg_inv(p, s, m)
}

// ---------------------------------------------------------------------------
// Init, step, and induction over executions
// ---------------------------------------------------------------------------

pub proof fn lemma_inv_init(p: Params, s: State)
    requires
        init(p, s),
    ensures
        inv(p, s),
{
    assert forall|d: int| 0 <= d < p.ndev implies #[trigger] dev_inv(p, s, d) by {}
}

pub proof fn lemma_inv_step(p: Params, rule: Rule, s: State, a: Action, s2: State)
    requires
        const_assumptions(p),
        inv(p, s),
        step(p, rule, s, a, s2),
    ensures
        inv(p, s2),
{
    match a {
        Action::RegChange { d, to } => {
            assert forall|i: int| 0 <= i < p.ndev implies #[trigger] dev_inv(p, s2, i) by {
                assert(dev_inv(p, s, i));
            }
            assert forall|m: Msg| s2.net.contains(m) implies #[trigger] msg_inv(p, s2, m) by {
                assert(msg_inv(p, s, m));
            }
        },
        Action::PushNotify { d, t } => {
            assert forall|i: int| 0 <= i < p.ndev implies #[trigger] dev_inv(p, s2, i) by {
                assert(dev_inv(p, s, i));
            }
            assert forall|m: Msg| s2.net.contains(m) implies #[trigger] msg_inv(p, s2, m) by {
                if s.net.contains(m) {
                    assert(msg_inv(p, s, m));
                } else {
                    assert(dev_inv(p, s, d as int));
                }
            }
        },
        Action::DeliverNotify { m } => {
            assert(msg_inv(p, s, m));
            assert forall|i: int| 0 <= i < p.ndev implies #[trigger] dev_inv(p, s2, i) by {
                assert(dev_inv(p, s, i));
            }
            assert forall|m2: Msg| s2.net.contains(m2) implies #[trigger] msg_inv(p, s2, m2) by {
                assert(msg_inv(p, s, m2));
            }
        },
        Action::DropNotify { m } => {
            assert forall|i: int| 0 <= i < p.ndev implies #[trigger] dev_inv(p, s2, i) by {
                assert(dev_inv(p, s, i));
            }
            assert forall|m2: Msg| s2.net.contains(m2) implies #[trigger] msg_inv(p, s2, m2) by {
                assert(msg_inv(p, s, m2));
            }
        },
        Action::Tick => {
            assert forall|i: int| 0 <= i < p.ndev implies #[trigger] dev_inv(p, s2, i) by {
                assert(dev_inv(p, s, i));
            }
            assert forall|m: Msg| s2.net.contains(m) implies #[trigger] msg_inv(p, s2, m) by {
                assert(msg_inv(p, s, m));
            }
        },
        _ => {
            assert forall|i: int| 0 <= i < p.ndev implies #[trigger] dev_inv(p, s2, i) by {
                assert(dev_inv(p, s, i));
            }
            assert forall|m: Msg| s2.net.contains(m) implies #[trigger] msg_inv(p, s2, m) by {
                assert(msg_inv(p, s, m));
            }
        },
    }
}

proof fn lemma_inv_prefix(p: Params, rule: Rule, ss: Seq<State>, acts: Seq<Action>, i: int)
    requires
        const_assumptions(p),
        is_execution(p, rule, ss, acts),
        0 <= i < ss.len(),
    ensures
        inv(p, ss[i]),
    decreases i,
{
    if i == 0 {
        lemma_inv_init(p, ss[0]);
    } else {
        lemma_inv_prefix(p, rule, ss, acts, i - 1);
        let j = i - 1;
        assert(step(p, rule, ss[j], acts[j], ss[j + 1]));
        lemma_inv_step(p, rule, ss[j], acts[j], ss[j + 1]);
    }
}

/// Every reachable state satisfies the invariant (executions of any length).
pub proof fn lemma_reachable_inv(p: Params, rule: Rule, s: State)
    requires
        const_assumptions(p),
        reachable(p, rule, s),
    ensures
        inv(p, s),
{
    let (ss, acts) = choose|ss: Seq<State>, acts: Seq<Action>|
        #[trigger] is_execution(p, rule, ss, acts) && ss.last() == s;
    lemma_inv_prefix(p, rule, ss, acts, ss.len() - 1);
}

pub proof fn lemma_paper_params_ok()
    ensures
        const_assumptions(paper_params()),
        paper_params().skew <= paper_params().skewbound,
        paper_params().maxt <= u64::MAX,
{
}

// ---------------------------------------------------------------------------
// ✓ cells that hold in EVERY state (no invariant needed), for all Params
// ---------------------------------------------------------------------------

/// S3 for A4 and A6: these rules require reg[d] = "Enrolled", contradicting reg[d] = "Revoked".
pub proof fn lemma_cell_s3_a4(p: Params) ensures cell_holds(p, Rule::A4, Prop::S3) {}
pub proof fn lemma_cell_s3_a6(p: Params) ensures cell_holds(p, Rule::A6, Prop::S3) {}

/// S1, S2, S6, AV for A4 and A6: A4 = link Up /\ reg[d] = "Enrolled" (and A6 adds NoCritical).
pub proof fn lemma_cell_s1_a4(p: Params) ensures cell_holds(p, Rule::A4, Prop::S1) {}
pub proof fn lemma_cell_s1_a6(p: Params) ensures cell_holds(p, Rule::A6, Prop::S1) {}
pub proof fn lemma_cell_s2_a4(p: Params) ensures cell_holds(p, Rule::A4, Prop::S2) {}
pub proof fn lemma_cell_s2_a6(p: Params) ensures cell_holds(p, Rule::A6, Prop::S2) {}
pub proof fn lemma_cell_s6_a4(p: Params) ensures cell_holds(p, Rule::A4, Prop::S6) {}
pub proof fn lemma_cell_s6_a6(p: Params) ensures cell_holds(p, Rule::A6, Prop::S6) {}
pub proof fn lemma_cell_av_a4(p: Params) ensures cell_holds(p, Rule::A4, Prop::AV) {}
pub proof fn lemma_cell_av_a6(p: Params) ensures cell_holds(p, Rule::A6, Prop::AV) {}
/// S4 for A4 and A6: reg[d] = "Absent" contradicts reg[d] = "Enrolled".
pub proof fn lemma_cell_s4_a4(p: Params) ensures cell_holds(p, Rule::A4, Prop::S4) {}
pub proof fn lemma_cell_s4_a6(p: Params) ensures cell_holds(p, Rule::A6, Prop::S4) {}

/// S5 for A5, A6, A7, A8: these rules include NoCritical(d), the negation of S5's premise.
pub proof fn lemma_cell_s5_a5(p: Params) ensures cell_holds(p, Rule::A5, Prop::S5) {}
pub proof fn lemma_cell_s5_a6(p: Params) ensures cell_holds(p, Rule::A6, Prop::S5) {}
pub proof fn lemma_cell_s5_a7(p: Params) ensures cell_holds(p, Rule::A7, Prop::S5) {}
pub proof fn lemma_cell_s5_a8(p: Params) ensures cell_holds(p, Rule::A8, Prop::S5) {}

// ---------------------------------------------------------------------------
// ✓ cells proved from the invariant
// ---------------------------------------------------------------------------

/// S3 for A8 (the paper's main result), for every Params with SKEW <= SKEWBOUND
/// and clock values that fit the code's u64. The arithmetic step is P5
/// (lemmas.rs), applied to the code's entry type: the model's
/// OriginPrecedesRevocation is exactly P5's hypothesis.
pub proof fn lemma_cell_s3_a8(p: Params)
    requires
        const_assumptions(p),
        p.skew <= p.skewbound,
        p.maxt <= u64::MAX,
    ensures
        cell_holds(p, Rule::A8, Prop::S3),
{
    crate::lemmas::lemma_p5_soundness_core();
    assert forall|s: State| #[trigger] reachable(p, Rule::A8, s) implies prop_holds(p, Rule::A8, Prop::S3, s) by {
        lemma_reachable_inv(p, Rule::A8, s);
        assert forall|d: nat| d < p.ndev implies
            ((s.reg[d as int] == RegSt::Revoked && s.since_rev[d as int] > p.lease)
                ==> !#[trigger] allow_rule(p, Rule::A8, s, d)) by {
            assert(dev_inv(p, s, d as int));
            if s.reg[d as int] == RegSt::Revoked && allow_rule(p, Rule::A8, s, d) {
                // the code's view of slot d, and P5 with sigma = SKEW
                let e = Entry { status: Status::Enrolled, ver: 0, orig: s.pdp_orig[d as int] as u64 };
                let now = s.now as u64;
                let delta = p.lease as u64;
                let sigma_hat = p.skewbound as u64;
                assert(a8(e, now, delta, sigma_hat, false));
                assert(p5_instance(e, now, delta, sigma_hat, false, s.since_rev[d as int] as int, p.skew as int));
                assert(s.since_rev[d as int] <= p.lease);
            }
        }
    }
}

/// S4 for the cache- and device-based rules A1, A2, A3, A5, A7, A8, for all Params:
/// reg[d] = "Absent" => regVer[d] = 0 => pdpVer[d] = 0 => pdpSt[d] = "Absent",
/// and reg[d] = "Absent" => dev[d] = "Unprov".
pub proof fn lemma_cell_s4(p: Params, rule: Rule)
    requires
        const_assumptions(p),
    ensures
        cell_holds(p, rule, Prop::S4),
{
    assert forall|s: State| #[trigger] reachable(p, rule, s) implies prop_holds(p, rule, Prop::S4, s) by {
        lemma_reachable_inv(p, rule, s);
        assert forall|d: nat| d < p.ndev implies
            (s.reg[d as int] == RegSt::Absent ==> !#[trigger] allow_rule(p, rule, s, d)) by {
            assert(dev_inv(p, s, d as int));
        }
    }
}

/// AVPD for A2: CacheMatchesCurrentVersion gives pdpSt[d] = reg[d] = "Enrolled".
pub proof fn lemma_cell_avpd_a2(p: Params)
    requires
        const_assumptions(p),
    ensures
        cell_holds(p, Rule::A2, Prop::AVPD),
{
    assert forall|s: State| #[trigger] reachable(p, Rule::A2, s) implies prop_holds(p, Rule::A2, Prop::AVPD, s) by {
        lemma_reachable_inv(p, Rule::A2, s);
        assert forall|d: nat| d < p.ndev implies
            ((s.reg[d as int] == RegSt::Enrolled && no_critical(p, s, d)
                && s.pdp_ver[d as int] == s.reg_ver[d as int]
                && (s.now as int - s.pdp_orig[d as int] as int) <= p.lease as int - p.skewbound as int)
                ==> #[trigger] allow_rule(p, Rule::A2, s, d)) by {
            assert(dev_inv(p, s, d as int));
        }
    }
}

/// AVPD for A8: as A2, and A8's horizon is exactly AVPD's (RuleHorizon = LEASE - SKEWBOUND).
pub proof fn lemma_cell_avpd_a8(p: Params)
    requires
        const_assumptions(p),
    ensures
        cell_holds(p, Rule::A8, Prop::AVPD),
{
    assert forall|s: State| #[trigger] reachable(p, Rule::A8, s) implies prop_holds(p, Rule::A8, Prop::AVPD, s) by {
        lemma_reachable_inv(p, Rule::A8, s);
        assert forall|d: nat| d < p.ndev implies
            ((s.reg[d as int] == RegSt::Enrolled && no_critical(p, s, d)
                && s.pdp_ver[d as int] == s.reg_ver[d as int]
                && (s.now as int - s.pdp_orig[d as int] as int) <= p.lease as int - p.skewbound as int)
                ==> #[trigger] allow_rule(p, Rule::A8, s, d)) by {
            assert(dev_inv(p, s, d as int));
        }
    }
}

/// AVPD for A3, for every Params with SKEW <= SKEWBOUND: pdpAge <= (now - pdpOrig) + SKEW.
pub proof fn lemma_cell_avpd_a3(p: Params)
    requires
        const_assumptions(p),
        p.skew <= p.skewbound,
    ensures
        cell_holds(p, Rule::A3, Prop::AVPD),
{
    assert forall|s: State| #[trigger] reachable(p, Rule::A3, s) implies prop_holds(p, Rule::A3, Prop::AVPD, s) by {
        lemma_reachable_inv(p, Rule::A3, s);
        assert forall|d: nat| d < p.ndev implies
            ((s.reg[d as int] == RegSt::Enrolled && no_critical(p, s, d)
                && s.pdp_ver[d as int] == s.reg_ver[d as int]
                && (s.now as int - s.pdp_orig[d as int] as int) <= p.lease as int - p.skewbound as int)
                ==> #[trigger] allow_rule(p, Rule::A3, s, d)) by {
            assert(dev_inv(p, s, d as int));
        }
    }
}

/// AVPD for A5, for every Params with SKEW <= SKEWBOUND: as A3, plus NoCritical from the premise.
pub proof fn lemma_cell_avpd_a5(p: Params)
    requires
        const_assumptions(p),
        p.skew <= p.skewbound,
    ensures
        cell_holds(p, Rule::A5, Prop::AVPD),
{
    assert forall|s: State| #[trigger] reachable(p, Rule::A5, s) implies prop_holds(p, Rule::A5, Prop::AVPD, s) by {
        lemma_reachable_inv(p, Rule::A5, s);
        assert forall|d: nat| d < p.ndev implies
            ((s.reg[d as int] == RegSt::Enrolled && no_critical(p, s, d)
                && s.pdp_ver[d as int] == s.reg_ver[d as int]
                && (s.now as int - s.pdp_orig[d as int] as int) <= p.lease as int - p.skewbound as int)
                ==> #[trigger] allow_rule(p, Rule::A5, s, d)) by {
            assert(dev_inv(p, s, d as int));
        }
    }
}

} // verus!

verus! {

// ---------------------------------------------------------------------------
// S7 (damage bound): rule-specific invariants
// ---------------------------------------------------------------------------

/// A7 at paper_params (one device): a grant the cache can still give.
pub open spec fn a7_grant_left(p: Params, s: State) -> bool {
    s.pdp_st[0] == RegSt::Enrolled && s.use_cnt[0] < p.maxuse
}

/// A7 at paper_params: an in-flight "Enrolled" notification that would still be
/// accepted (version newer than the cache's) and so would refill the grant budget.
pub open spec fn a7_pending(s: State) -> bool {
    exists|m: Msg| #[trigger] s.net.contains(m) && m.st == RegSt::Enrolled && m.ver > s.pdp_ver[0]
}

/// A7 at paper_params: damage so far plus damage still obtainable is at most 1.
/// (With MAXVER = 2 the registry's last change is to Suspended/Revoked at version 2;
/// after it, only a cached grant or one pending Enrolled notification can be used.)
pub open spec fn a7_budget(p: Params, s: State) -> bool {
    &&& ((s.reg[0] == RegSt::Absent || s.reg[0] == RegSt::Enrolled) ==> s.bad_grants[0] == 0)
    &&& ((s.reg[0] == RegSt::Suspended || s.reg[0] == RegSt::Revoked) ==>
            s.bad_grants[0] + (if a7_grant_left(p, s) { 1nat } else { 0nat })
                + (if a7_pending(s) { 1nat } else { 0nat }) <= 1)
}

pub open spec fn rule_inv(p: Params, rule: Rule, s: State) -> bool {
    match rule {
        Rule::A4 => forall|d: int| 0 <= d < p.ndev ==> #[trigger] s.bad_grants[d] == 0,
        Rule::A6 => forall|d: int| 0 <= d < p.ndev ==> #[trigger] s.bad_grants[d] == 0,
        Rule::A7 => p == paper_params() ==> a7_budget(p, s),
        _ => true,
    }
}

proof fn lemma_two_elems(net: Set<Msg>, a: Msg, b: Msg)
    requires
        net.contains(a),
        net.contains(b),
        a != b,
    ensures
        net.len() >= 2,
{
    let t = Set::<Msg>::empty().insert(a).insert(b);
    assert(t.subset_of(net));
    vstd::set_lib::lemma_len_subset(t, net);
    assert(!Set::<Msg>::empty().insert(a).contains(b));
}

proof fn lemma_a7_budget_step(p: Params, s: State, a: Action, s2: State)
    requires
        p == paper_params(),
        inv(p, s),
        inv(p, s2),
        a7_budget(p, s),
        step(p, Rule::A7, s, a, s2),
    ensures
        a7_budget(p, s2),
{
    assert(dev_inv(p, s, 0));
    assert(dev_inv(p, s2, 0));
    match a {
        Action::RegChange { d, to } => {
            if a7_pending(s) {
                let m = choose|m: Msg| #[trigger] s.net.contains(m) && m.st == RegSt::Enrolled && m.ver > s.pdp_ver[0];
                assert(msg_inv(p, s, m));
            }
            assert(a7_pending(s2) == a7_pending(s));
        },
        Action::PushNotify { d, t } => {
            if a7_pending(s2) && (s.reg[0] == RegSt::Suspended || s.reg[0] == RegSt::Revoked) {
                let m = choose|m: Msg| #[trigger] s2.net.contains(m) && m.st == RegSt::Enrolled && m.ver > s2.pdp_ver[0];
                // the pushed message reports reg[d] (d = 0, the only device), which is not Enrolled
                assert(d == 0);
                assert(s.net.contains(m));
                assert(a7_pending(s));
            }
        },
        Action::DeliverNotify { m } => {
            assert(msg_inv(p, s, m));
            if a7_pending(s2) {
                let m2 = choose|m2: Msg| #[trigger] s2.net.contains(m2) && m2.st == RegSt::Enrolled && m2.ver > s2.pdp_ver[0];
                assert(s.net.contains(m2) && m2 != m);
                lemma_two_elems(s.net, m, m2);
                assert(false);
            }
            if m.ver > s.pdp_ver[0] && m.st == RegSt::Enrolled {
                assert(a7_pending(s));
            }
        },
        Action::DropNotify { m } => {
            if a7_pending(s2) {
                let m2 = choose|m2: Msg| #[trigger] s2.net.contains(m2) && m2.st == RegSt::Enrolled && m2.ver > s2.pdp_ver[0];
                assert(s.net.contains(m2));
                assert(a7_pending(s));
            }
        },
        Action::PdpPoll { d } => {
            if a7_pending(s2) {
                let m2 = choose|m2: Msg| #[trigger] s2.net.contains(m2) && m2.st == RegSt::Enrolled && m2.ver > s2.pdp_ver[0];
                assert(msg_inv(p, s, m2));
                assert(false);
            }
        },
        Action::RecordAccess { d } => {
            assert(a7_pending(s2) == a7_pending(s));
        },
        Action::Tick => {
            assert(a7_pending(s2) == a7_pending(s));
        },
        _ => {
            assert(a7_pending(s2) == a7_pending(s));
        },
    }
}

pub proof fn lemma_rule_inv_init(p: Params, rule: Rule, s: State)
    requires
        init(p, s),
    ensures
        rule_inv(p, rule, s),
{
    if rule == Rule::A7 && p == paper_params() {
        assert(!a7_pending(s));
    }
}

pub proof fn lemma_rule_inv_step(p: Params, rule: Rule, s: State, a: Action, s2: State)
    requires
        const_assumptions(p),
        inv(p, s),
        rule_inv(p, rule, s),
        step(p, rule, s, a, s2),
    ensures
        rule_inv(p, rule, s2),
{
    lemma_inv_step(p, rule, s, a, s2);
    match rule {
        Rule::A7 => {
            if p == paper_params() {
                lemma_a7_budget_step(p, s, a, s2);
            }
        },
        _ => {},
    }
}

proof fn lemma_rule_inv_prefix(p: Params, rule: Rule, ss: Seq<State>, acts: Seq<Action>, i: int)
    requires
        const_assumptions(p),
        is_execution(p, rule, ss, acts),
        0 <= i < ss.len(),
    ensures
        inv(p, ss[i]),
        rule_inv(p, rule, ss[i]),
    decreases i,
{
    if i == 0 {
        lemma_inv_init(p, ss[0]);
        lemma_rule_inv_init(p, rule, ss[0]);
    } else {
        lemma_rule_inv_prefix(p, rule, ss, acts, i - 1);
        let j = i - 1;
        assert(step(p, rule, ss[j], acts[j], ss[j + 1]));
        lemma_inv_step(p, rule, ss[j], acts[j], ss[j + 1]);
        lemma_rule_inv_step(p, rule, ss[j], acts[j], ss[j + 1]);
    }
}

pub proof fn lemma_reachable_rule_inv(p: Params, rule: Rule, s: State)
    requires
        const_assumptions(p),
        reachable(p, rule, s),
    ensures
        inv(p, s),
        rule_inv(p, rule, s),
{
    let (ss, acts) = choose|ss: Seq<State>, acts: Seq<Action>|
        #[trigger] is_execution(p, rule, ss, acts) && ss.last() == s;
    lemma_rule_inv_prefix(p, rule, ss, acts, ss.len() - 1);
}

/// S7 for A4 and A6, for all Params with MAXBAD > 0: these rules grant only
/// when reg[d] = "Enrolled", so RecordAccess never increments badGrants.
pub proof fn lemma_cell_s7_a4(p: Params)
    requires const_assumptions(p), p.maxbad > 0,
    ensures cell_holds(p, Rule::A4, Prop::S7),
{
    assert forall|s: State| #[trigger] reachable(p, Rule::A4, s) implies prop_holds(p, Rule::A4, Prop::S7, s) by {
        lemma_reachable_rule_inv(p, Rule::A4, s);
    }
}

pub proof fn lemma_cell_s7_a6(p: Params)
    requires const_assumptions(p), p.maxbad > 0,
    ensures cell_holds(p, Rule::A6, Prop::S7),
{
    assert forall|s: State| #[trigger] reachable(p, Rule::A6, s) implies prop_holds(p, Rule::A6, Prop::S7, s) by {
        lemma_reachable_rule_inv(p, Rule::A6, s);
    }
}

/// S7 for A7, in the paper's configuration only (badGrants <= 1 < MAXBAD = 3).
/// The general bound depends on MAXUSE, MAXVER and MAXNET (see the model's
/// DamageBelow2/DamageBelow3, L490-493); it is not claimed here.
pub proof fn lemma_cell_s7_a7()
    ensures cell_holds(paper_params(), Rule::A7, Prop::S7),
{
    let p = paper_params();
    assert forall|s: State| #[trigger] reachable(p, Rule::A7, s) implies prop_holds(p, Rule::A7, Prop::S7, s) by {
        lemma_reachable_rule_inv(p, Rule::A7, s);
        assert(dev_inv(p, s, 0));
        assert forall|d: nat| d < p.ndev implies #[trigger] s.bad_grants[d as int] < p.maxbad by {}
    }
}

} // verus!
