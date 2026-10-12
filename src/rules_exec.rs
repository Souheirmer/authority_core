//! Extension A, step 2: executable rules A1-A8, each proved equal to its spec
//! function in rules_spec.rs. Inputs are the state components the rule reads,
//! as machine integers; `critical_active` is `~NoCritical(d)` (L165).
//! A8 delegates to the verified decision function of the original crate
//! (decide::allow, P3).
use vstd::prelude::*;
use crate::spec::{Entry, Status};
use crate::decide::allow;
use crate::system_spec::*;
use crate::rules_spec::*;

verus! {

/// What the rules read about one device d, as the code sees it.
pub struct RuleInputs {
    pub dev: DevSt,
    pub reg: RegSt,
    pub pdp_st: RegSt,
    pub pdp_age: u64,
    pub pdp_orig: u64,
    pub use_cnt: u64,
    pub now: u64,
    pub link: Link,
    pub critical_active: bool,
}

/// Configuration constants the rules read.
pub struct RuleConsts {
    pub lease: u64,
    pub skewbound: u64,
    pub maxuse: u64,
}

/// `x` describes device d of state s under parameters p.
pub open spec fn inputs_match(x: RuleInputs, k: RuleConsts, p: Params, s: State, d: nat) -> bool {
    &&& x.dev == s.dev[d as int]
    &&& x.reg == s.reg[d as int]
    &&& x.pdp_st == s.pdp_st[d as int]
    &&& x.pdp_age as nat == s.pdp_age[d as int]
    &&& x.pdp_orig as nat == s.pdp_orig[d as int]
    &&& x.use_cnt as nat == s.use_cnt[d as int]
    &&& x.now as nat == s.now
    &&& x.link == s.link
    &&& x.critical_active == !no_critical(p, s, d)
    &&& k.lease as nat == p.lease
    &&& k.skewbound as nat == p.skewbound
    &&& k.maxuse as nat == p.maxuse
}

fn is_enrolled(st: &RegSt) -> (b: bool)
    ensures b == (*st == RegSt::Enrolled),
{
    match st { RegSt::Enrolled => true, _ => false }
}

pub fn exec_a1(x: &RuleInputs) -> (b: bool)
    ensures forall|p: Params, s: State, d: nat, k: RuleConsts|
        #[trigger] inputs_match(*x, k, p, s, d) ==> b == a1_local(p, s, d),
{
    match x.dev { DevSt::Prov => true, _ => false }
}

pub fn exec_a2(x: &RuleInputs) -> (b: bool)
    ensures forall|p: Params, s: State, d: nat, k: RuleConsts|
        #[trigger] inputs_match(*x, k, p, s, d) ==> b == a2_pdp_cache(p, s, d),
{
    is_enrolled(&x.pdp_st)
}

pub fn exec_a3(x: &RuleInputs, k: &RuleConsts) -> (b: bool)
    ensures forall|p: Params, s: State, d: nat|
        #[trigger] inputs_match(*x, *k, p, s, d) ==> b == a3_lease(p, s, d),
{
    is_enrolled(&x.pdp_st) && x.pdp_age <= k.lease
}

pub fn exec_a4(x: &RuleInputs) -> (b: bool)
    ensures forall|p: Params, s: State, d: nat, k: RuleConsts|
        #[trigger] inputs_match(*x, k, p, s, d) ==> b == a4_fail_closed(p, s, d),
{
    let up = match x.link { Link::Up => true, Link::Down => false };
    up && is_enrolled(&x.reg)
}

pub fn exec_a5(x: &RuleInputs, k: &RuleConsts) -> (b: bool)
    ensures forall|p: Params, s: State, d: nat|
        #[trigger] inputs_match(*x, *k, p, s, d) ==> b == a5_lease_ctx(p, s, d),
{
    exec_a3(x, k) && !x.critical_active
}

pub fn exec_a6(x: &RuleInputs) -> (b: bool)
    ensures forall|p: Params, s: State, d: nat, k: RuleConsts|
        #[trigger] inputs_match(*x, k, p, s, d) ==> b == a6_fail_closed_ctx(p, s, d),
{
    exec_a4(x) && !x.critical_active
}

pub fn exec_a7(x: &RuleInputs, k: &RuleConsts) -> (b: bool)
    ensures forall|p: Params, s: State, d: nat|
        #[trigger] inputs_match(*x, *k, p, s, d) ==> b == a7_count_lease(p, s, d),
{
    is_enrolled(&x.pdp_st) && x.use_cnt < k.maxuse && !x.critical_active
}

/// A8 via the verified decision function of the original crate. Equal to the
/// model's A8 under ConstAssumptions' SKEWBOUND <= LEASE (L81); the code's a8
/// additionally denies when sigma_hat > delta.
pub fn exec_a8(x: &RuleInputs, k: &RuleConsts) -> (b: bool)
    ensures forall|p: Params, s: State, d: nat|
        #[trigger] inputs_match(*x, *k, p, s, d) && p.skewbound <= p.lease ==> b == a8_origin_lease(p, s, d),
{
    let status = match x.pdp_st {
        RegSt::Absent => Status::Unknown,
        RegSt::Enrolled => Status::Enrolled,
        RegSt::Suspended => Status::Suspended,
        RegSt::Revoked => Status::Revoked,
    };
    let e = Entry { status, ver: 0, orig: x.pdp_orig };
    allow(&e, x.now, k.lease, k.skewbound, x.critical_active)
}

/// AllowRule(d) (L198-206).
pub fn exec_allow_rule(rule: &Rule, x: &RuleInputs, k: &RuleConsts) -> (b: bool)
    ensures forall|p: Params, s: State, d: nat|
        #[trigger] inputs_match(*x, *k, p, s, d) && p.skewbound <= p.lease ==> b == allow_rule(p, *rule, s, d),
{
    match rule {
        Rule::A1 => exec_a1(x),
        Rule::A2 => exec_a2(x),
        Rule::A3 => exec_a3(x, k),
        Rule::A4 => exec_a4(x),
        Rule::A5 => exec_a5(x, k),
        Rule::A6 => exec_a6(x),
        Rule::A7 => exec_a7(x, k),
        Rule::A8 => exec_a8(x, k),
    }
}

} // verus!
