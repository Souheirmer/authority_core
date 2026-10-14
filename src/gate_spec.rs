//! Spec of the D witness (command gate under configuration uncertainty).
//! A small feasibility witness for the "verified command gate" proposal, not
//! the proposed component: one replaced asset, a bounded set of feeders, two
//! command scopes. Human approval required before merge (SPEC_CHANGES.md).
use vstd::prelude::*;

verus! {

/// Feeders an asset can be connected to, and assets behind the gate.
pub const FEEDERS: usize = 4;
pub const ASSETS: usize = 8;

/// Per asset: the current device incarnation and the candidate set of feeders
/// it may be on (cand[x] = "feeder x is still possible").
#[derive(Clone, Copy)]
pub struct AssetState {
    pub incarnation: u64,
    pub cand: [bool; FEEDERS],
}

/// SiteWide: permitted whatever feeder the asset is on (e.g. site-wide
/// curtailment). Feeder(f): permitted only if the asset is on feeder f
/// (e.g. a feeder-specific setpoint).
#[derive(Clone, Copy)]
pub enum Scope {
    SiteWide,
    Feeder(u8),
}

/// A command bound to an asset, an exact incarnation, a scope, and the
/// origin deadline of its grant. ASSUMPTION: this authority/deadline metadata
/// is trusted input; it is not an authenticated grant in this witness.
#[derive(Clone, Copy)]
pub struct Command {
    pub asset: u32,
    pub incarnation: u64,
    pub scope: Scope,
    pub deadline: u64,
}

/// `Admitted` means admitted at the gate, nothing more: it does not mean
/// delivered, executed or accepted by the controller.
pub enum Decision {
    Admitted,
    Withheld,
}

pub open spec fn permitted_in(scope: Scope, feeder: int) -> bool {
    match scope {
        Scope::SiteWide => true,
        Scope::Feeder(f) => f as int == feeder,
    }
}

pub open spec fn cand_nonempty(cand: Seq<bool>) -> bool {
    exists|x: int| 0 <= x < FEEDERS as int && #[trigger] cand[x]
}

pub open spec fn permitted_everywhere(scope: Scope, cand: Seq<bool>) -> bool {
    forall|x: int| 0 <= x < FEEDERS as int && #[trigger] cand[x] ==> permitted_in(scope, x)
}

/// G1, the admission rule: in range, grant not expired at `now`, exact
/// incarnation, at least one candidate (fail closed on an empty set), and
/// permitted in EVERY candidate configuration.
pub open spec fn admit_spec(g: Seq<AssetState>, c: Command, now: u64) -> bool {
    &&& (c.asset as int) < (ASSETS as int)
    &&& now <= c.deadline
    &&& c.incarnation == g[c.asset as int].incarnation
    &&& cand_nonempty(g[c.asset as int].cand@)
    &&& permitted_everywhere(c.scope, g[c.asset as int].cand@)
}

/// Replacement of asset a (managed): new incarnation; the candidate set is
/// WIDENED by every feeder the manifest allows (`allowed`); never narrowed.
pub open spec fn replace_post(old: Seq<AssetState>, new: Seq<AssetState>, a: int, allowed: Seq<bool>) -> bool {
    &&& new.len() == old.len()
    &&& forall|i: int| 0 <= i < old.len() && i != a ==> #[trigger] new[i] == old[i]
    &&& new[a].incarnation == old[a].incarnation + 1
    &&& forall|x: int| 0 <= x < FEEDERS as int ==> #[trigger] new[a].cand@[x] == (old[a].cand@[x] || allowed[x])
}

/// Assumed-current truthful evidence that asset a (current incarnation) is on
/// feeder f prunes its candidate set to {f}. ASSUMPTION: the evidence is true
/// now for the current incarnation; signatures and chronology are not checked
/// in this witness.
pub open spec fn prune_post(old: Seq<AssetState>, new: Seq<AssetState>, a: int, f: int) -> bool {
    &&& new.len() == old.len()
    &&& forall|i: int| 0 <= i < old.len() && i != a ==> #[trigger] new[i] == old[i]
    &&& new[a].incarnation == old[a].incarnation
    &&& forall|x: int| 0 <= x < FEEDERS as int ==> #[trigger] new[a].cand@[x] == (x == f)
}

} // verus!
