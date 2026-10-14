//! A witness: the proposal's first-sprint cases as tests (not proofs).
//! Signature results are trusted inputs here; no cryptography is done.
use authority_core::update::UpdatePolicy;
use authority_core::update_spec::{Mode, Role, Transcript};

const CLASS: u32 = 7;
const IMG: u64 = 0xA11CE;

fn t(counter: u64, epoch: u64) -> Transcript {
    Transcript { class: CLASS, digest: IMG, counter, epoch, key_c: 1, key_pq: 2 }
}

fn hybrid() -> UpdatePolicy {
    let mut p = UpdatePolicy::new(CLASS);
    assert!(p.migrate(Mode::Hybrid, Role::PolicyAuthority)); // epoch 2
    p
}

#[test]
fn hybrid_image_with_both_signatures_is_admitted() {
    let p = hybrid();
    assert!(p.check_admission(&t(5, 2), IMG, true, true));
}

#[test]
fn stripped_signature_is_rejected() {
    let p = hybrid();
    assert!(!p.check_admission(&t(5, 2), IMG, true, false));
    assert!(!p.check_admission(&t(5, 2), IMG, false, true));
}

#[test]
fn retired_key_is_rejected() {
    let mut p = hybrid();
    assert!(p.retire(1, Role::PolicyAuthority));
    assert!(!p.check_admission(&t(5, 2), IMG, true, true));
}

#[test]
fn firmware_key_cannot_change_policy() {
    let mut p = hybrid();
    assert!(!p.retire(2, Role::Firmware));
    assert!(!p.migrate(Mode::PostQuantum, Role::Firmware));
    assert!(!p.migrate(Mode::Classical, Role::PolicyAuthority)); // never back
    assert!(p.check_admission(&t(5, 2), IMG, true, true));
}

#[test]
fn other_image_other_device_and_old_epoch_are_rejected() {
    let p = hybrid();
    assert!(!p.check_admission(&t(5, 2), IMG + 1, true, true));
    let mut other = t(5, 2);
    other.class = CLASS + 1;
    assert!(!p.check_admission(&other, IMG, true, true));
    assert!(!p.check_admission(&t(5, 1), IMG, true, true)); // pre-migration policy
}

#[test]
fn below_floor_is_rejected_after_commit() {
    let mut p = hybrid();
    p.commit(5);
    assert!(!p.check_admission(&t(4, 2), IMG, true, true));
    assert!(p.check_admission(&t(5, 2), IMG, true, true));
    p.commit(3); // never decreases
    assert!(!p.check_admission(&t(4, 2), IMG, true, true));
}
