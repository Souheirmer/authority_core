//! D witness: the worked trace from the proposal, as a test (not a proof).
//! Asset 0 is replaced; until assumed-current truthful evidence says which feeder it is on,
//! it may be on F1 or F2. The proved rule is admit_spec (src/gate_spec.rs).
use authority_core::gate::Gate;
use authority_core::gate_spec::{Command, Decision, Scope};

const F1: u8 = 1;
const F2: u8 = 2;
const NOW: u64 = 1_000;
const DEADLINE: u64 = 1_090;

fn cmd(asset: u32, incarnation: u64, scope: Scope) -> Command {
    Command { asset, incarnation, scope, deadline: DEADLINE }
}

fn admitted(g: &Gate, c: Command, now: u64) -> bool {
    matches!(g.decide(&c, now), Decision::Admitted)
}

/// Asset 0 known on F1, asset 1 known on F2 (assumed-current truthful evidence).
fn site() -> Gate {
    let mut g = Gate::new();
    g.prune(0, F1);
    g.prune(1, F2);
    g
}

#[test]
fn worked_trace_replacement_with_ambiguous_feeder() {
    let mut g = site();
    assert!(admitted(&g, cmd(0, 1, Scope::Feeder(F1)), NOW));

    // Managed replacement of asset 0; the manifest allows F1 or F2.
    g.replace(0, &[false, true, true, false]);

    // Site-wide curtailment to the current incarnation: admitted.
    assert!(admitted(&g, cmd(0, 2, Scope::SiteWide), NOW));
    // Feeder-specific setpoint while F2 is still possible: withheld.
    assert!(!admitted(&g, cmd(0, 2, Scope::Feeder(F1)), NOW));
    assert!(!admitted(&g, cmd(0, 2, Scope::Feeder(F2)), NOW));
    // Retired incarnation: withheld, even site-wide.
    assert!(!admitted(&g, cmd(0, 1, Scope::SiteWide), NOW));
    // Asset 1 does not depend on asset 0's feeder: unaffected.
    assert!(admitted(&g, cmd(1, 1, Scope::Feeder(F2)), NOW));

    // Assumed-current truthful evidence: the replacement is on F1. Now the F1 setpoint passes.
    g.prune(0, F1);
    assert!(admitted(&g, cmd(0, 2, Scope::Feeder(F1)), NOW));
    assert!(!admitted(&g, cmd(0, 2, Scope::Feeder(F2)), NOW));
}

#[test]
fn expired_grant_is_withheld() {
    let g = site();
    assert!(admitted(&g, cmd(0, 1, Scope::SiteWide), DEADLINE));
    assert!(!admitted(&g, cmd(0, 1, Scope::SiteWide), DEADLINE + 1));
}

#[test]
fn out_of_range_asset_is_withheld() {
    let g = site();
    assert!(!admitted(&g, cmd(8, 1, Scope::SiteWide), NOW));
}

#[test]
fn feeder_specific_command_is_withheld_under_initial_uncertainty() {
    // Before any evidence every feeder is possible.
    let g = Gate::new();
    assert!(admitted(&g, cmd(3, 1, Scope::SiteWide), NOW));
    assert!(!admitted(&g, cmd(3, 1, Scope::Feeder(0)), NOW));
}
