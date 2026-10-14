//! B witness: the proposal's scenario as a test (not a proof). A service
//! engineer's grant is issued at t = 1000 with origin deadline 1090; the
//! switch is cut off from its controller. The proved rules are in
//! src/fabric_spec.rs.
use authority_core::fabric::Switch;
use authority_core::fabric_spec::Rule;

const ENGINEER: u32 = 0;
const OPERATOR: u32 = 1;

#[test]
fn delayed_installation_does_not_extend_the_origin_deadline() {
    let mut sw = Switch::new();
    let grant = Rule { boot: 1, deadline: 1090 };
    // The controller only manages to install the rule at 1080 (delayed).
    assert!(sw.install(ENGINEER, grant, 1080));
    // Controller lost from here on. The rule still ends at the ORIGIN deadline;
    // an installation-timed rule with a 90 s timer would run until 1170.
    assert!(sw.forward(ENGINEER, 1090));
    assert!(!sw.forward(ENGINEER, 1091));
    assert!(!sw.forward(ENGINEER, 1170));
}

#[test]
fn retried_installation_keeps_the_same_deadline() {
    let mut sw = Switch::new();
    let grant = Rule { boot: 1, deadline: 1090 };
    assert!(sw.install(ENGINEER, grant, 1010));
    assert!(sw.install(ENGINEER, grant, 1085)); // retry after reconnection
    assert!(!sw.forward(ENGINEER, 1091));
}

#[test]
fn late_rule_never_activates() {
    let mut sw = Switch::new();
    assert!(!sw.install(ENGINEER, Rule { boot: 1, deadline: 1090 }, 1100));
    assert!(!sw.forward(ENGINEER, 1100));
}

#[test]
fn fresh_grant_keeps_working_while_cut_off() {
    let mut sw = Switch::new();
    assert!(sw.install(OPERATOR, Rule { boot: 1, deadline: 1200 }, 1010));
    // Controller lost; no renewal arrives. Supervision continues until 1200.
    assert!(sw.forward(OPERATOR, 1150));
    assert!(sw.forward(OPERATOR, 1200));
    assert!(!sw.forward(OPERATOR, 1201));
}

#[test]
fn reboot_and_clock_loss_close_the_path() {
    let mut sw = Switch::new();
    assert!(sw.install(OPERATOR, Rule { boot: 1, deadline: 1200 }, 1010));
    sw.reboot();
    assert!(!sw.forward(OPERATOR, 1050));
    // A rule labelled for the old boot epoch is refused after the reboot.
    assert!(!sw.install(OPERATOR, Rule { boot: 1, deadline: 1200 }, 1060));
    assert!(sw.install(OPERATOR, Rule { boot: 2, deadline: 1200 }, 1060));
    assert!(sw.forward(OPERATOR, 1070));
    sw.clock_lost();
    assert!(!sw.forward(OPERATOR, 1080));
}
