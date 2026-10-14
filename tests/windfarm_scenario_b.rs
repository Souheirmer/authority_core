//! B on an emulated wind-farm scenario (tests on the proved switch rules, not
//! proofs, and not GE equipment or a real switch). An offshore farm switch
//! carries a vendor engineer's IEC 60870-5-104 service session to a turbine
//! controller and the operator's SCADA session from the control centre.
//! Times in seconds; grants issued at t = 0.
use authority_core::fabric::Switch;
use authority_core::fabric_spec::Rule;

const ENGINEER: u32 = 0; // vendor service session, 1-hour grant
const OPERATOR: u32 = 1; // control-centre SCADA session, 24-hour grant

#[test]
fn engineer_withdrawn_during_offshore_link_outage() {
    let mut sw = Switch::new();
    let engineer = Rule { boot: 1, deadline: 3_600 };
    let operator = Rule { boot: 1, deadline: 86_400 };
    assert!(sw.install(OPERATOR, operator, 5));
    // The engineer's rule only reaches the switch late, at t = 1 700.
    assert!(sw.install(ENGINEER, engineer, 1_700));
    // t = 1 800: the offshore link to the controller fails. No installs from now on.
    // t = 2 000: the operator withdraws the engineer's authority; the switch cannot be told.
    // The session still ends at its ORIGIN deadline (an installation-timed
    // 1-hour rule would have run to t = 5 300).
    assert!(sw.forward(ENGINEER, 3_600));
    assert!(!sw.forward(ENGINEER, 3_601));
    assert!(!sw.forward(ENGINEER, 5_300));
    // The operator's supervision continues through the outage.
    assert!(sw.forward(OPERATOR, 3_601));
    assert!(sw.forward(OPERATOR, 40_000));
}

#[test]
fn bounded_withdrawal_numbers() {
    // Issuer contract (assumed): a grant for authority withdrawn at t_w carries
    // deadline <= t_w + delta - sigma_hat. With t_w = 2 000, delta = 1 800 s,
    // sigma_hat = 10 s: 3 600 <= 3 790. Clock contract (assumed): switch clock
    // lags real time by at most 10 s. Then nothing forwards after real time
    // t_w + delta = 3 800, i.e. switch time >= 3 790 > 3 600.
    let mut sw = Switch::new();
    assert!(sw.install(ENGINEER, Rule { boot: 1, deadline: 3_600 }, 100));
    for switch_time in 3_790..3_900 {
        assert!(!sw.forward(ENGINEER, switch_time));
    }
}

#[test]
fn turbine_switch_reboot_closes_service_access() {
    let mut sw = Switch::new();
    assert!(sw.install(ENGINEER, Rule { boot: 1, deadline: 3_600 }, 100));
    sw.reboot(); // modelled operation
    assert!(!sw.forward(ENGINEER, 200));
}
