//! D on an emulated wind-farm scenario (tests on the proved gate, not proofs,
//! and not GE equipment). Eight turbines on two feeders: T0-T3 on F1,
//! T4-T7 on F2. A farm-wide curtailment is a site-wide-scoped command sent
//! to each turbine; a feeder setpoint is scoped to one feeder.
use authority_core::gate::Gate;
use authority_core::gate_spec::{Command, Decision, Scope};

const F1: u8 = 1;
const F2: u8 = 2;
const NOW: u64 = 10_000;
const GRANT_END: u64 = 10_900; // curtailment grant valid for 15 minutes

fn cmd(turbine: u32, incarnation: u64, scope: Scope) -> Command {
    Command { asset: turbine, incarnation, scope, deadline: GRANT_END }
}

fn ok(g: &Gate, c: Command, now: u64) -> bool {
    matches!(g.decide(&c, now), Decision::Admitted)
}

/// Commissioned farm: every turbine's feeder known (assumed-current truthful evidence).
fn farm() -> Gate {
    let mut g = Gate::new();
    for t in 0..4 { g.prune(t, F1); }
    for t in 4..8 { g.prune(t, F2); }
    g
}

#[test]
fn farm_wide_curtailment_with_a_replaced_turbine_controller() {
    let mut g = farm();
    // T3's controller is replaced; the manifest allows it on F1 or F2.
    g.replace(3, &[false, true, true, false]);

    // Grid operator asks for farm-wide curtailment: admitted for all eight
    // turbines, including T3's new controller.
    for t in 0..8 {
        let inc = if t == 3 { 2 } else { 1 };
        assert!(ok(&g, cmd(t, inc, Scope::SiteWide), NOW), "turbine {}", t);
    }
    // An F1 setpoint for T3 waits until its feeder is confirmed...
    assert!(!ok(&g, cmd(3, 2, Scope::Feeder(F1)), NOW));
    // ...while T0-T2 (F1) and T4-T7 (F2) are unaffected.
    for t in 0..3 { assert!(ok(&g, cmd(t, 1, Scope::Feeder(F1)), NOW)); }
    for t in 4..8 { assert!(ok(&g, cmd(t, 1, Scope::Feeder(F2)), NOW)); }
    // Commands addressed to the removed controller are refused.
    assert!(!ok(&g, cmd(3, 1, Scope::SiteWide), NOW));

    // Commissioning confirms T3 on F1: its F1 setpoint now passes.
    g.prune(3, F1);
    assert!(ok(&g, cmd(3, 2, Scope::Feeder(F1)), NOW));
    assert!(!ok(&g, cmd(3, 2, Scope::Feeder(F2)), NOW));
}

#[test]
fn curtailment_grant_expires() {
    let g = farm();
    assert!(ok(&g, cmd(0, 1, Scope::SiteWide), GRANT_END));
    assert!(!ok(&g, cmd(0, 1, Scope::SiteWide), GRANT_END + 1));
}
