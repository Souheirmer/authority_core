//! Extension A: authorization rules A1-A8 and properties S1-S7, AV, AVP, AVPD
//! of model/Provisioning.tla, transcribed into Verus spec functions.
//! Line numbers (`L123`) refer to Provisioning.tla. Conventions as in
//! system_spec.rs (devices and events numbered from 0; `-` over int).
use vstd::prelude::*;
use crate::system_spec::*;

verus! {

// ---------------------------------------------------------------------------
// Rules (L165-206)
// ---------------------------------------------------------------------------

/// RuleNames (L68-70)
pub enum Rule { A1, A2, A3, A4, A5, A6, A7, A8 }

/// NoCritical(d) == (activeEv[d] \cap CRITICAL) = {}   (L165)
pub open spec fn no_critical(p: Params, s: State, d: nat) -> bool {
    s.active_ev[d as int].intersect(p.critical) == Set::<nat>::empty()
}

/// A1_Local(d) == dev[d] = "Prov"   (L167)
pub open spec fn a1_local(p: Params, s: State, d: nat) -> bool {
    s.dev[d as int] == DevSt::Prov
}

/// A2_PdpCache(d) == pdpSt[d] = "Enrolled"   (L168)
pub open spec fn a2_pdp_cache(p: Params, s: State, d: nat) -> bool {
    s.pdp_st[d as int] == RegSt::Enrolled
}

/// A3_Lease(d) == pdpSt[d] = "Enrolled" /\ pdpAge[d] <= LEASE   (L169)
pub open spec fn a3_lease(p: Params, s: State, d: nat) -> bool {
    s.pdp_st[d as int] == RegSt::Enrolled && s.pdp_age[d as int] <= p.lease
}

/// A4_FailClosed(d) == link = "Up" /\ reg[d] = "Enrolled"   (L170)
pub open spec fn a4_fail_closed(p: Params, s: State, d: nat) -> bool {
    s.link == Link::Up && s.reg[d as int] == RegSt::Enrolled
}

/// A5_LeaseCtx(d) == A3_Lease(d) /\ NoCritical(d)   (L171)
pub open spec fn a5_lease_ctx(p: Params, s: State, d: nat) -> bool {
    a3_lease(p, s, d) && no_critical(p, s, d)
}

/// A6_FailClosedCtx(d) == A4_FailClosed(d) /\ NoCritical(d)   (L172)
pub open spec fn a6_fail_closed_ctx(p: Params, s: State, d: nat) -> bool {
    a4_fail_closed(p, s, d) && no_critical(p, s, d)
}

/// A7_CountLease(d) == pdpSt[d] = "Enrolled" /\ useCnt[d] < MAXUSE /\ NoCritical(d)   (L177-179)
pub open spec fn a7_count_lease(p: Params, s: State, d: nat) -> bool {
    &&& s.pdp_st[d as int] == RegSt::Enrolled
    &&& s.use_cnt[d as int] < p.maxuse
    &&& no_critical(p, s, d)
}

/// RuleHorizon == LEASE - SKEWBOUND   (L191). Nat-valued under ConstAssumptions
/// (SKEWBOUND <= LEASE, L81); written over int as TLC evaluates it.
pub open spec fn rule_horizon(p: Params) -> int {
    p.lease as int - p.skewbound as int
}

/// A8_OriginLease(d) == pdpSt[d] = "Enrolled" /\ (now - pdpOrig[d]) <= RuleHorizon
///                      /\ NoCritical(d)   (L194-196)
pub open spec fn a8_origin_lease(p: Params, s: State, d: nat) -> bool {
    &&& s.pdp_st[d as int] == RegSt::Enrolled
    &&& (s.now as int - s.pdp_orig[d as int] as int) <= rule_horizon(p)
    &&& no_critical(p, s, d)
}

/// AllowRule(d) (L198-206)
pub open spec fn allow_rule(p: Params, rule: Rule, s: State, d: nat) -> bool {
    match rule {
        Rule::A1 => a1_local(p, s, d),
        Rule::A2 => a2_pdp_cache(p, s, d),
        Rule::A3 => a3_lease(p, s, d),
        Rule::A4 => a4_fail_closed(p, s, d),
        Rule::A5 => a5_lease_ctx(p, s, d),
        Rule::A6 => a6_fail_closed_ctx(p, s, d),
        Rule::A7 => a7_count_lease(p, s, d),
        Rule::A8 => a8_origin_lease(p, s, d),
    }
}

// ---------------------------------------------------------------------------
// Properties (L459-521). Each quantifies over d \in DEVICES = {0..ndev-1}.
// ---------------------------------------------------------------------------

/// S1_AuthoritativeSoundness (L460-461)
pub open spec fn s1(p: Params, rule: Rule, s: State) -> bool {
    forall|d: nat| d < p.ndev ==> (#[trigger] allow_rule(p, rule, s, d) ==> s.reg[d as int] == RegSt::Enrolled)
}

/// S2_ImmediateRevocation (L464-465)
pub open spec fn s2(p: Params, rule: Rule, s: State) -> bool {
    forall|d: nat| d < p.ndev ==> (s.reg[d as int] == RegSt::Revoked ==> !#[trigger] allow_rule(p, rule, s, d))
}

/// S3_BoundedRevocation (L471-473)
pub open spec fn s3(p: Params, rule: Rule, s: State) -> bool {
    forall|d: nat| d < p.ndev ==>
        ((s.reg[d as int] == RegSt::Revoked && s.since_rev[d as int] > p.lease)
            ==> !#[trigger] allow_rule(p, rule, s, d))
}

/// S4_DenyAbsent (L475-476)
pub open spec fn s4(p: Params, rule: Rule, s: State) -> bool {
    forall|d: nat| d < p.ndev ==> (s.reg[d as int] == RegSt::Absent ==> !#[trigger] allow_rule(p, rule, s, d))
}

/// S5_ContextDenial (L478-479)
pub open spec fn s5(p: Params, rule: Rule, s: State) -> bool {
    forall|d: nat| d < p.ndev ==>
        (s.active_ev[d as int].intersect(p.critical) != Set::<nat>::empty()
            ==> !#[trigger] allow_rule(p, rule, s, d))
}

/// S6_DenySuspended (L481-482)
pub open spec fn s6(p: Params, rule: Rule, s: State) -> bool {
    forall|d: nat| d < p.ndev ==> (s.reg[d as int] == RegSt::Suspended ==> !#[trigger] allow_rule(p, rule, s, d))
}

/// S7_DamageBounded (L487-488)
pub open spec fn s7(p: Params, rule: Rule, s: State) -> bool {
    forall|d: nat| d < p.ndev ==> #[trigger] s.bad_grants[d as int] < p.maxbad
}

/// AV_Availability (L502-504)
pub open spec fn av(p: Params, rule: Rule, s: State) -> bool {
    forall|d: nat| d < p.ndev ==>
        ((s.link == Link::Up && s.reg[d as int] == RegSt::Enrolled && no_critical(p, s, d))
            ==> #[trigger] allow_rule(p, rule, s, d))
}

/// AVP_AvailUnderPartition (L507-509)
pub open spec fn avp(p: Params, rule: Rule, s: State) -> bool {
    forall|d: nat| d < p.ndev ==>
        ((s.reg[d as int] == RegSt::Enrolled && no_critical(p, s, d))
            ==> #[trigger] allow_rule(p, rule, s, d))
}

/// AVPD_BoundedAvailUnderPartition (L517-521)
pub open spec fn avpd(p: Params, rule: Rule, s: State) -> bool {
    forall|d: nat| d < p.ndev ==>
        ((s.reg[d as int] == RegSt::Enrolled && no_critical(p, s, d)
            && s.pdp_ver[d as int] == s.reg_ver[d as int]
            && (s.now as int - s.pdp_orig[d as int] as int) <= p.lease as int - p.skewbound as int)
            ==> #[trigger] allow_rule(p, rule, s, d))
}

pub enum Prop { S1, S2, S3, S4, S5, S6, S7, AV, AVP, AVPD }

pub open spec fn prop_holds(p: Params, rule: Rule, prop: Prop, s: State) -> bool {
    match prop {
        Prop::S1 => s1(p, rule, s),
        Prop::S2 => s2(p, rule, s),
        Prop::S3 => s3(p, rule, s),
        Prop::S4 => s4(p, rule, s),
        Prop::S5 => s5(p, rule, s),
        Prop::S6 => s6(p, rule, s),
        Prop::S7 => s7(p, rule, s),
        Prop::AV => av(p, rule, s),
        Prop::AVP => avp(p, rule, s),
        Prop::AVPD => avpd(p, rule, s),
    }
}

// ---------------------------------------------------------------------------
// The table: what a cell means
// ---------------------------------------------------------------------------

/// A ✓ cell: the property holds in every reachable state (any number of steps).
pub open spec fn cell_holds(p: Params, rule: Rule, prop: Prop) -> bool {
    forall|s: State| #[trigger] reachable(p, rule, s) ==> prop_holds(p, rule, prop, s)
}

/// A ✗ cell: some finite execution from Init ends in a state violating it.
/// (Evidence: a concrete execution checked by Verus.)
pub open spec fn cell_violated(p: Params, rule: Rule, prop: Prop) -> bool {
    exists|s: State| #[trigger] reachable(p, rule, s) && !prop_holds(p, rule, prop, s)
}

/// The paper's table (model/EXPECTED_RESULTS.md), for comparison only. true = ✓.
pub open spec fn paper_expected(rule: Rule, prop: Prop) -> bool {
    match prop {
        // S1, S2, S6, AV:  ✓ only for A4, A6
        Prop::S1 | Prop::S2 | Prop::S6 | Prop::AV => rule == Rule::A4 || rule == Rule::A6,
        // S3:  ✓ for A4, A6, A8
        Prop::S3 => rule == Rule::A4 || rule == Rule::A6 || rule == Rule::A8,
        // S4:  ✓ for all
        Prop::S4 => true,
        // S5:  ✓ for A5, A6, A7, A8
        Prop::S5 => rule == Rule::A5 || rule == Rule::A6 || rule == Rule::A7 || rule == Rule::A8,
        // S7:  ✓ for A4, A6, A7
        Prop::S7 => rule == Rule::A4 || rule == Rule::A6 || rule == Rule::A7,
        // AVP: ✗ for all
        Prop::AVP => false,
        // AVPD: ✓ for A2, A3, A5, A8
        Prop::AVPD => rule == Rule::A2 || rule == Rule::A3 || rule == Rule::A5 || rule == Rule::A8,
    }
}

} // verus!
