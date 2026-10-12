//! Extension A: the 8x10 table, machine-checked against the paper.
//! For every (rule, property): if the paper says ✓ the property holds in every
//! reachable state, and if it says ✗ a violating execution exists, in the
//! paper's configuration.
use vstd::prelude::*;
use crate::system_spec::*;
use crate::rules_spec::*;
use crate::rules_proofs::*;
use crate::rules_cex::*;

verus! {

/// A cell cannot be both ✓ and ✗ (so the table below is consistent).
pub proof fn lemma_cells_exclusive(p: Params, rule: Rule, prop: Prop)
    ensures
        !(cell_holds(p, rule, prop) && cell_violated(p, rule, prop)),
{
}

pub open spec fn table_cell_ok(rule: Rule, prop: Prop) -> bool {
    if paper_expected(rule, prop) {
        cell_holds(paper_params(), rule, prop)
    } else {
        cell_violated(paper_params(), rule, prop)
    }
}

pub proof fn lemma_table_cell(rule: Rule, prop: Prop)
    ensures
        table_cell_ok(rule, prop),
{
    let p = paper_params();
    lemma_paper_params_ok();
    match prop {
        Prop::S1 => match rule {
            Rule::A1 => lemma_cell_s1_a1_violated(),
            Rule::A4 => lemma_cell_s1_a4(p),
            Rule::A6 => lemma_cell_s1_a6(p),
            _ => lemma_cell_cache_rules_violated(rule, prop),
        },
        Prop::S2 => match rule {
            Rule::A1 => lemma_cell_s2_a1_violated(),
            Rule::A4 => lemma_cell_s2_a4(p),
            Rule::A6 => lemma_cell_s2_a6(p),
            _ => lemma_cell_cache_rules_violated(rule, prop),
        },
        Prop::S3 => match rule {
            Rule::A1 => lemma_cell_s3_a1_violated(),
            Rule::A2 => lemma_cell_s3_a2_violated(),
            Rule::A3 => lemma_cell_s3_a3_violated(),
            Rule::A4 => lemma_cell_s3_a4(p),
            Rule::A5 => lemma_cell_s3_a5_violated(),
            Rule::A6 => lemma_cell_s3_a6(p),
            Rule::A7 => lemma_cell_s3_a7_violated(),
            Rule::A8 => lemma_cell_s3_a8(p),
        },
        Prop::S4 => match rule {
            Rule::A4 => lemma_cell_s4_a4(p),
            Rule::A6 => lemma_cell_s4_a6(p),
            _ => lemma_cell_s4(p, rule),
        },
        Prop::S5 => match rule {
            Rule::A1 => lemma_cell_s5_a1_violated(),
            Rule::A2 => lemma_cell_s5_a2_violated(),
            Rule::A3 => lemma_cell_s5_a3_violated(),
            Rule::A4 => lemma_cell_s5_a4_violated(),
            Rule::A5 => lemma_cell_s5_a5(p),
            Rule::A6 => lemma_cell_s5_a6(p),
            Rule::A7 => lemma_cell_s5_a7(p),
            Rule::A8 => lemma_cell_s5_a8(p),
        },
        Prop::S6 => match rule {
            Rule::A1 => lemma_cell_s6_a1_violated(),
            Rule::A4 => lemma_cell_s6_a4(p),
            Rule::A6 => lemma_cell_s6_a6(p),
            _ => lemma_cell_cache_rules_violated(rule, prop),
        },
        Prop::S7 => match rule {
            Rule::A1 => lemma_cell_s7_a1_violated(),
            Rule::A4 => lemma_cell_s7_a4(p),
            Rule::A6 => lemma_cell_s7_a6(p),
            Rule::A7 => lemma_cell_s7_a7(),
            _ => lemma_cell_s7_cache_violated(rule),
        },
        Prop::AV => match rule {
            Rule::A4 => lemma_cell_av_a4(p),
            Rule::A6 => lemma_cell_av_a6(p),
            _ => lemma_cell_av_avp_violated(rule, prop),
        },
        Prop::AVP => match rule {
            Rule::A4 => lemma_cell_avp_failclosed_violated(rule),
            Rule::A6 => lemma_cell_avp_failclosed_violated(rule),
            _ => lemma_cell_av_avp_violated(rule, prop),
        },
        Prop::AVPD => match rule {
            Rule::A1 => lemma_cell_avpd_a1_violated(),
            Rule::A2 => lemma_cell_avpd_a2(p),
            Rule::A3 => lemma_cell_avpd_a3(p),
            Rule::A4 => lemma_cell_avpd_a4_violated(),
            Rule::A5 => lemma_cell_avpd_a5(p),
            Rule::A6 => lemma_cell_avpd_a6_violated(),
            Rule::A7 => lemma_cell_avpd_a7_violated(),
            Rule::A8 => lemma_cell_avpd_a8(p),
        },
    }
}

/// THE TABLE: all 80 cells agree with model/EXPECTED_RESULTS.md.
pub proof fn lemma_paper_table()
    ensures
        forall|rule: Rule, prop: Prop| #[trigger] table_cell_ok(rule, prop),
{
    assert forall|rule: Rule, prop: Prop| #[trigger] table_cell_ok(rule, prop) by {
        lemma_table_cell(rule, prop);
    }
}

} // verus!
