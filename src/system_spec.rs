//! Extension A: the transition system of model/Provisioning.tla, transcribed
//! into Verus spec functions. Line numbers (`L123`) refer to Provisioning.tla.
//!
//! Transcription conventions (the only deviations in form, none in meaning):
//! * DEVICES = {0, ..., ndev-1} and EVENTTYPES = {0, ..., nev-1}; the model's
//!   model values d1, d2, ... / e1, e2, ... are numbered from 0. Every function
//!   over DEVICES is a Seq of length ndev.
//! * Numbers are `nat`, as in TLA+'s Naturals. Subtraction that can go
//!   negative in the model (`now - pdpOrig[d]`, `t - now`) is written over
//!   `int`, which is how TLC and TLAPS evaluate `-` (Naturals' `-` is integer
//!   subtraction).
//! * `Next` (L359-371) is a disjunction of existentially quantified actions.
//!   Here each disjunct is an `Action` value carrying its bound variables
//!   (d, to, t, m, e), and `next` is `exists a. step(a)`. `PushNotify`'s
//!   `\E t \in 0..MAXT` (L239) becomes the action parameter `t`.
//! * Each action is written as a guard plus the post-state, listing every
//!   variable, so UNCHANGED is explicit.
//! * Fairness (L389-450) and liveness (L537-542) are not transcribed: all ten
//!   properties of the table are state invariants.
use vstd::prelude::*;
use crate::rules_spec::*;

verus! {

// ---------------------------------------------------------------------------
// Constants (L53-66) and ASSUME ConstAssumptions (L72-81)
// ---------------------------------------------------------------------------

pub struct Params {
    pub ndev: nat,          // |DEVICES|
    pub nev: nat,           // |EVENTTYPES|
    pub critical: Set<nat>, // CRITICAL
    pub lease: nat,         // LEASE (Delta)
    pub maxage: nat,        // MAXAGE
    pub maxver: nat,        // MAXVER
    pub maxnet: nat,        // MAXNET
    pub maxuse: nat,        // MAXUSE
    pub maxbad: nat,        // MAXBAD
    pub maxt: nat,          // MAXT
    pub skew: nat,          // SKEW (sigma)
    pub skewbound: nat,     // SKEWBOUND (sigma_hat)
}

/// ConstAssumptions (L72-81); `RULE \in RuleNames` holds by typing (enum Rule).
pub open spec fn const_assumptions(p: Params) -> bool {
    &&& p.ndev > 0                                         // DEVICES # {}
    &&& p.nev > 0                                          // EVENTTYPES # {}
    &&& forall|e: nat| p.critical.contains(e) ==> e < p.nev // CRITICAL \subseteq EVENTTYPES
    &&& p.maxage > p.lease
    &&& p.maxt >= p.maxage
    &&& p.skewbound <= p.lease
}

/// The paper's default configuration (model/EXPECTED_RESULTS.md, and every
/// cfg in model/tlc_configs/<rule>__<property>.cfg): DEVICES = {d1},
/// EVENTTYPES = {e1}, CRITICAL = {e1}, LEASE = 1, MAXAGE = 3, MAXVER = 2,
/// MAXNET = 1, MAXUSE = 1, MAXBAD = 3, MAXT = 3, SKEW = SKEWBOUND = 0.
pub open spec fn paper_params() -> Params {
    Params {
        ndev: 1, nev: 1, critical: set![0nat],
        lease: 1, maxage: 3, maxver: 2, maxnet: 1, maxuse: 1, maxbad: 3, maxt: 3,
        skew: 0, skewbound: 0,
    }
}

// ---------------------------------------------------------------------------
// Value sets (L83-85) and notifications (L108)
// ---------------------------------------------------------------------------

/// RegStates (L83)
pub enum RegSt { Absent, Enrolled, Suspended, Revoked }

/// DevStates (L84)
pub enum DevSt { Unprov, Prov, Inv }

/// LinkStates (L85)
pub enum Link { Up, Down }

/// Notification == [dv: DEVICES, st: RegStates, ver: 0..MAXVER, orig: 0..MAXT] (L108)
pub struct Msg { pub dv: nat, pub st: RegSt, pub ver: nat, pub orig: nat }

// ---------------------------------------------------------------------------
// State (VARIABLES, L87-102)
// ---------------------------------------------------------------------------

pub struct State {
    pub reg: Seq<RegSt>,          // reg[d]        authoritative registry state (ground truth)
    pub reg_ver: Seq<nat>,        // regVer[d]
    pub dev: Seq<DevSt>,          // dev[d]        device-local cached view
    pub pdp_st: Seq<RegSt>,       // pdpSt[d]      decision point's cached registry state
    pub pdp_ver: Seq<nat>,        // pdpVer[d]
    pub pdp_age: Seq<nat>,        // pdpAge[d]     ticks since the cache was WRITTEN
    pub pdp_orig: Seq<nat>,       // pdpOrig[d]    clock value at which the data was OBSERVED
    pub since_rev: Seq<nat>,      // sinceRev[d]   ticks since reg[d] became Revoked
    pub now: nat,                 // now           global logical clock
    pub use_cnt: Seq<nat>,        // useCnt[d]
    pub bad_grants: Seq<nat>,     // badGrants[d]
    pub link: Link,               // link
    pub net: Set<Msg>,            // net           notifications in flight
    pub active_ev: Seq<Set<nat>>, // activeEv[d]   active runtime events
}

/// The domains of the functions over DEVICES (implied by TypeOK, L123-139).
pub open spec fn state_shape(p: Params, s: State) -> bool {
    &&& s.reg.len() == p.ndev && s.reg_ver.len() == p.ndev && s.dev.len() == p.ndev
    &&& s.pdp_st.len() == p.ndev && s.pdp_ver.len() == p.ndev && s.pdp_age.len() == p.ndev
    &&& s.pdp_orig.len() == p.ndev && s.since_rev.len() == p.ndev && s.use_cnt.len() == p.ndev
    &&& s.bad_grants.len() == p.ndev && s.active_ev.len() == p.ndev
}

// ---------------------------------------------------------------------------
// Init (L141-155)
// ---------------------------------------------------------------------------

pub open spec fn init(p: Params, s: State) -> bool {
    &&& s.reg == Seq::new(p.ndev, |d: int| RegSt::Absent)
    &&& s.reg_ver == Seq::new(p.ndev, |d: int| 0nat)
    &&& s.dev == Seq::new(p.ndev, |d: int| DevSt::Unprov)
    &&& s.pdp_st == Seq::new(p.ndev, |d: int| RegSt::Absent)
    &&& s.pdp_ver == Seq::new(p.ndev, |d: int| 0nat)
    &&& s.pdp_age == Seq::new(p.ndev, |d: int| 0nat)
    &&& s.pdp_orig == Seq::new(p.ndev, |d: int| 0nat)
    &&& s.since_rev == Seq::new(p.ndev, |d: int| 0nat)
    &&& s.now == 0
    &&& s.use_cnt == Seq::new(p.ndev, |d: int| 0nat)
    &&& s.bad_grants == Seq::new(p.ndev, |d: int| 0nat)
    &&& s.link == Link::Up
    &&& s.net == Set::<Msg>::empty()
    &&& s.active_ev == Seq::new(p.ndev, |d: int| Set::<nat>::empty())
}

// ---------------------------------------------------------------------------
// Actions (L212-357)
// ---------------------------------------------------------------------------

pub enum Action {
    RegChange { d: nat, to: RegSt },     // L217
    PushNotify { d: nat, t: nat },       // L234 (t: the existential witness of L239)
    DeliverNotify { m: Msg },            // L247
    DropNotify { m: Msg },               // L261
    PdpPoll { d: nat },                  // L268
    SyncFromRegistry { d: nat },         // L291
    ObserveEvent { d: nat, e: nat },     // L296
    ClearEvent { d: nat, e: nat },       // L303
    RecordAccess { d: nat },             // L349
    Tick,                                // L310
    Partition,                           // L323
    Heal,                                // L328
}

/// RegTransition(from, to) (L212-215)
pub open spec fn reg_transition(from: RegSt, to: RegSt) -> bool {
    ||| (from == RegSt::Absent && to == RegSt::Enrolled)
    ||| (from == RegSt::Enrolled && (to == RegSt::Suspended || to == RegSt::Revoked))
    ||| (from == RegSt::Suspended && (to == RegSt::Enrolled || to == RegSt::Revoked))
}

/// DevViewOf(r) (L285-289)
pub open spec fn dev_view_of(r: RegSt) -> DevSt {
    match r {
        RegSt::Enrolled => DevSt::Prov,
        RegSt::Revoked => DevSt::Inv,
        RegSt::Suspended => DevSt::Inv,
        _ => DevSt::Unprov,
    }
}

/// Saturating increment used by Tick (L313-318) and RecordAccess (L351-352).
pub open spec fn sat_inc(x: nat, bound: nat) -> nat {
    if x + 1 > bound { bound } else { x + 1 }
}

/// The quantifier ranges of Next (L360-368): d \in DEVICES, e \in EVENTTYPES,
/// to \in RegStates (by typing), m \in net, and t \in 0..MAXT (L239).
pub open spec fn action_in_range(p: Params, s: State, a: Action) -> bool {
    match a {
        Action::RegChange { d, to } => d < p.ndev,
        Action::PushNotify { d, t } => d < p.ndev && t <= p.maxt,
        Action::DeliverNotify { m } => s.net.contains(m),
        Action::DropNotify { m } => s.net.contains(m),
        Action::PdpPoll { d } => d < p.ndev,
        Action::SyncFromRegistry { d } => d < p.ndev,
        Action::ObserveEvent { d, e } => d < p.ndev && e < p.nev,
        Action::ClearEvent { d, e } => d < p.ndev && e < p.nev,
        Action::RecordAccess { d } => d < p.ndev,
        Action::Tick => true,
        Action::Partition => true,
        Action::Heal => true,
    }
}

/// The enabling condition of each action (the conjuncts that do not mention
/// primed variables).
pub open spec fn enabled(p: Params, rule: Rule, s: State, a: Action) -> bool {
    match a {
        // L218-219
        Action::RegChange { d, to } =>
            s.reg_ver[d as int] < p.maxver && reg_transition(s.reg[d as int], to),
        // L235-236, L240
        Action::PushNotify { d, t } =>
            s.link == Link::Up && s.net.len() < p.maxnet  // vstd Sets are finite; len = Cardinality
            && t as int - s.now as int <= p.skew as int
            && s.now as int - t as int <= p.skew as int,
        // L248 (m \in net is in action_in_range)
        Action::DeliverNotify { m } => true,
        // L262
        Action::DropNotify { m } => true,
        // L269
        Action::PdpPoll { d } => s.link == Link::Up,
        Action::SyncFromRegistry { d } => true,
        // L298
        Action::ObserveEvent { d, e } => !s.active_ev[d as int].contains(e),
        // L304
        Action::ClearEvent { d, e } => s.active_ev[d as int].contains(e),
        // L350
        Action::RecordAccess { d } => allow_rule(p, rule, s, d),
        // L311
        Action::Tick => s.now < p.maxt,
        // L324
        Action::Partition => s.link == Link::Up,
        // L329
        Action::Heal => s.link == Link::Down,
    }
}

/// The post-state of each action. Fields not mentioned are UNCHANGED.
pub open spec fn effect(p: Params, s: State, a: Action) -> State {
    match a {
        // RegChange (L217-224)
        Action::RegChange { d, to } => State {
            reg: s.reg.update(d as int, to),
            reg_ver: s.reg_ver.update(d as int, s.reg_ver[d as int] + 1),
            since_rev: if to == RegSt::Revoked { s.since_rev.update(d as int, 0) } else { s.since_rev },
            ..s
        },
        // PushNotify (L234-244)
        Action::PushNotify { d, t } => State {
            net: s.net.insert(Msg { dv: d, st: s.reg[d as int], ver: s.reg_ver[d as int], orig: t }),
            ..s
        },
        // DeliverNotify (L247-258): monotonic reads
        Action::DeliverNotify { m } => {
            let s1 = State { net: s.net.remove(m), ..s };
            if m.ver > s.pdp_ver[m.dv as int] {
                State {
                    pdp_st: s.pdp_st.update(m.dv as int, m.st),
                    pdp_ver: s.pdp_ver.update(m.dv as int, m.ver),
                    pdp_age: s.pdp_age.update(m.dv as int, 0),
                    pdp_orig: s.pdp_orig.update(m.dv as int, m.orig),  // the ORIGIN travels with the data
                    use_cnt: s.use_cnt.update(m.dv as int, 0),
                    ..s1
                }
            } else {
                s1
            }
        },
        // DropNotify (L261-265)
        Action::DropNotify { m } => State { net: s.net.remove(m), ..s },
        // PdpPoll (L268-279)
        Action::PdpPoll { d } => State {
            pdp_st: s.pdp_st.update(d as int, s.reg[d as int]),
            pdp_ver: s.pdp_ver.update(d as int, s.reg_ver[d as int]),
            pdp_age: s.pdp_age.update(d as int, 0),
            pdp_orig: s.pdp_orig.update(d as int, s.now),  // stamped with the decision point's own clock
            use_cnt: s.use_cnt.update(d as int, 0),
            ..s
        },
        // SyncFromRegistry (L291-294)
        Action::SyncFromRegistry { d } => State {
            dev: s.dev.update(d as int, dev_view_of(s.reg[d as int])),
            ..s
        },
        // ObserveEvent (L296-301)
        Action::ObserveEvent { d, e } => State {
            active_ev: s.active_ev.update(d as int, s.active_ev[d as int].insert(e)),
            ..s
        },
        // ClearEvent (L303-307)
        Action::ClearEvent { d, e } => State {
            active_ev: s.active_ev.update(d as int, s.active_ev[d as int].remove(e)),
            ..s
        },
        // RecordAccess (L349-357)
        Action::RecordAccess { d } => State {
            use_cnt: s.use_cnt.update(d as int, sat_inc(s.use_cnt[d as int], p.maxuse)),
            bad_grants: s.bad_grants.update(d as int,
                if s.reg[d as int] == RegSt::Enrolled || s.bad_grants[d as int] == p.maxbad {
                    s.bad_grants[d as int]
                } else {
                    s.bad_grants[d as int] + 1
                }),
            ..s
        },
        // Tick (L310-320)
        Action::Tick => State {
            now: s.now + 1,
            pdp_age: Seq::new(p.ndev, |d: int| sat_inc(s.pdp_age[d], p.maxage)),
            since_rev: Seq::new(p.ndev, |d: int|
                if s.reg[d] != RegSt::Revoked { s.since_rev[d] } else { sat_inc(s.since_rev[d], p.maxage) }),
            ..s
        },
        // Partition (L323-326)
        Action::Partition => State { link: Link::Down, ..s },
        // Heal (L328-331)
        Action::Heal => State { link: Link::Up, ..s },
    }
}

/// One step of Next (L359-371) taken by action `a`.
pub open spec fn step(p: Params, rule: Rule, s: State, a: Action, s2: State) -> bool {
    &&& action_in_range(p, s, a)
    &&& enabled(p, rule, s, a)
    &&& s2 == effect(p, s, a)
}

/// Next (L359-371)
pub open spec fn next(p: Params, rule: Rule, s: State, s2: State) -> bool {
    exists|a: Action| #[trigger] step(p, rule, s, a, s2)
}

// ---------------------------------------------------------------------------
// Executions and reachability (Spec == Init /\ [][Next]_vars, L399)
// ---------------------------------------------------------------------------

/// A finite execution: states ss[0..n], actions acts[0..n-1].
/// (Stuttering steps of [Next]_vars change nothing and are omitted.)
pub open spec fn is_execution(p: Params, rule: Rule, ss: Seq<State>, acts: Seq<Action>) -> bool {
    &&& ss.len() == acts.len() + 1
    &&& init(p, ss[0])
    &&& forall|i: int| 0 <= i < acts.len() ==> #[trigger] step(p, rule, ss[i], acts[i], ss[i + 1])
}

pub open spec fn reachable(p: Params, rule: Rule, s: State) -> bool {
    exists|ss: Seq<State>, acts: Seq<Action>|
        #[trigger] is_execution(p, rule, ss, acts) && ss.last() == s
}

} // verus!
