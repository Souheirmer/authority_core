//! D witness: properties of the admission rule (G2-G5).
use vstd::prelude::*;
use crate::gate_spec::*;

verus! {

/// G2 soundness under uncertainty: if the actual feeder is among the
/// candidates, an admitted command is permitted in the actual configuration
/// under the simplified feeder predicate `permitted_in`. This is not physical
/// safety and says nothing about execution.
pub proof fn lemma_g2_actual_config(g: Seq<AssetState>, c: Command, now: u64, actual: int)
    requires
        admit_spec(g, c, now),
        0 <= actual < FEEDERS as int,
        g[c.asset as int].cand@[actual],
    ensures
        permitted_in(c.scope, actual),
{
}

/// G3 usefulness (non-vacuity): under exactly the lemma's preconditions (asset
/// in range, now <= deadline, current incarnation, non-empty candidate set,
/// site-wide scope), the command is admitted however uncertain the feeder is.
/// A deny-all gate fails this.
pub proof fn lemma_g3_sitewide_admitted(g: Seq<AssetState>, c: Command, now: u64)
    requires
        (c.asset as int) < (ASSETS as int),
        now <= c.deadline,
        c.incarnation == g[c.asset as int].incarnation,
        cand_nonempty(g[c.asset as int].cand@),
        c.scope is SiteWide,
    ensures
        admit_spec(g, c, now),
{
}

/// G3': a feeder-specific command is withheld while a second feeder is
/// still possible.
pub proof fn lemma_g3_ambiguous_feeder_withheld(g: Seq<AssetState>, c: Command, now: u64, other: int)
    requires
        0 <= other < FEEDERS as int,
        (c.asset as int) < (ASSETS as int),
        g[c.asset as int].cand@[other],
        c.scope matches Scope::Feeder(f) && f as int != other,
    ensures
        !admit_spec(g, c, now),
{
}

/// G4 containment: replacement never drops a possible feeder, and adds every
/// feeder the manifest allows; assumed-current truthful evidence keeps the actual feeder.
pub proof fn lemma_g4_replace_contains(old: Seq<AssetState>, new: Seq<AssetState>, a: int, allowed: Seq<bool>, x: int)
    requires
        replace_post(old, new, a, allowed),
        0 <= x < FEEDERS as int,
        old[a].cand@[x] || allowed[x],
    ensures
        new[a].cand@[x],
{
}

pub proof fn lemma_g4_truthful_prune_contains(old: Seq<AssetState>, new: Seq<AssetState>, a: int, actual: int)
    requires
        prune_post(old, new, a, actual),
        0 <= actual < FEEDERS as int,
    ensures
        new[a].cand@[actual],
{
}

/// G5 retired incarnation: after a replacement, a command bound to the old
/// incarnation is withheld.
pub proof fn lemma_g5_retired_incarnation(old: Seq<AssetState>, new: Seq<AssetState>, a: int, allowed: Seq<bool>, c: Command, now: u64)
    requires
        replace_post(old, new, a, allowed),
        0 <= a < old.len(),
        c.asset as int == a,
        c.incarnation == old[a].incarnation,
    ensures
        !admit_spec(new, c, now),
{
}

} // verus!
