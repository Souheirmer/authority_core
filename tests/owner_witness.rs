//! C witness: resale with a power cut and a restart, as tests (not proofs).
//! Chain verification is a trusted input; restart recovers from an assumed
//! persisted record (no physical storage is modelled).
use authority_core::owner::Device;
use authority_core::owner_spec::Transfer;

const DEV: u64 = 42;
const OLD_OWNER: u64 = 100;
const NEW_OWNER: u64 = 200;

fn tx(instance: u64, new_owner: u64) -> Transfer {
    Transfer { device: DEV, instance, new_owner, chain_ok: true }
}

#[test]
fn transfer_commits_and_retired_instance_is_refused_after_restart() {
    let mut d = Device::new(DEV, OLD_OWNER);
    assert!(d.begin(&tx(1, NEW_OWNER)));
    assert_eq!(d.owner, OLD_OWNER); // staged, not authoritative
    assert!(d.commit());
    assert_eq!(d.owner, NEW_OWNER);
    d.restart();
    // The old owner replays a voucher bound to the retired instance 1.
    assert!(!d.begin(&tx(1, OLD_OWNER)));
    assert_eq!(d.owner, NEW_OWNER);
}

#[test]
fn power_cut_before_commit_returns_to_prior_owner() {
    let mut d = Device::new(DEV, OLD_OWNER);
    assert!(d.begin(&tx(1, NEW_OWNER)));
    d.restart();
    assert_eq!(d.owner, OLD_OWNER);
    assert!(!d.commit()); // nothing staged any more
    assert_eq!(d.instance, 1);
}

#[test]
fn cross_device_and_unverified_chains_are_refused() {
    let mut d = Device::new(DEV, OLD_OWNER);
    let mut other = tx(1, NEW_OWNER);
    other.device = DEV + 1;
    assert!(!d.begin(&other));
    let mut broken = tx(1, NEW_OWNER);
    broken.chain_ok = false;
    assert!(!d.begin(&broken));
    assert!(!d.commit());
    assert_eq!(d.owner, OLD_OWNER);
}
