//! Extension A: proofs of the ✓ cells. One rule-independent inductive
//! invariant (`inv`) over the transition system of system_spec.rs, proved
//! for executions of any length; each ✓ cell follows from it.
//! The invariant's conjuncts are those of the model's IndInv (L631-644)
//! that the cells need, plus two clock facts (marked NEW).
use vstd::prelude::*;
use crate::spec::*;
use crate::system_spec::*;
use crate::rules_spec::*;
use crate::lemmas::lemma_p5_soundness_core;

verus! {

// ---------------------------------------------------------------------------
// The invariant
// ---------------------------------------------------------------------------

/// Per-device conjuncts.
pub open spec fn dev_inv(p: Params, s: State, d: int) -> bool {
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
    lemma_p5_soundness_core();
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
