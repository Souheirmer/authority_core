//! D witness: executable gate (G1 decision, replacement, pruning).
use vstd::prelude::*;
use crate::gate_spec::*;

verus! {

pub struct Gate {
    pub assets: [AssetState; ASSETS],
}

impl View for Gate {
    type V = Seq<AssetState>;

    open spec fn view(&self) -> Seq<AssetState> {
        self.assets@
    }
}

impl Gate {
    /// Every asset at incarnation 1 with every feeder possible (maximal
    /// uncertainty until assumed-current truthful evidence prunes it).
    pub fn new() -> (g: Self)
        ensures
            g@.len() == ASSETS,
            forall|i: int| 0 <= i < ASSETS as int ==> (#[trigger] g@[i]).incarnation == 1,
            forall|i: int, x: int| 0 <= i < ASSETS as int && 0 <= x < FEEDERS as int ==> #[trigger] g@[i].cand@[x],
    {
        Gate { assets: [AssetState { incarnation: 1, cand: [true; FEEDERS] }; ASSETS] }
    }

    /// G1: admitted iff admit_spec.
    pub fn decide(&self, c: &Command, now: u64) -> (d: Decision)
        ensures
            (d is Admitted) == admit_spec(self@, *c, now),
    {
        if c.asset as usize >= ASSETS {
            return Decision::Withheld;
        }
        let a = c.asset as usize;
        if now > c.deadline || c.incarnation != self.assets[a].incarnation {
            return Decision::Withheld;
        }
        let cand = self.assets[a].cand;
        let mut any = false;
        let mut all_ok = true;
        let mut x: usize = 0;
        while x < FEEDERS
            invariant
                0 <= x <= FEEDERS,
                cand@ == self@[a as int].cand@,
                any == (exists|y: int| 0 <= y < x as int && #[trigger] cand@[y]),
                all_ok == (forall|y: int| 0 <= y < x as int && #[trigger] cand@[y] ==> permitted_in(c.scope, y)),
            decreases FEEDERS - x,
        {
            if cand[x] {
                assert(cand@[x as int]);
                any = true;
                let ok = match c.scope {
                    Scope::SiteWide => true,
                    Scope::Feeder(f) => f as usize == x,
                };
                if !ok {
                    assert(!permitted_in(c.scope, x as int));
                    all_ok = false;
                }
            }
            x = x + 1;
        }
        if any && all_ok {
            Decision::Admitted
        } else {
            Decision::Withheld
        }
    }

    /// Managed replacement of asset a: new incarnation, candidate set widened.
    pub fn replace(&mut self, a: u32, allowed: &[bool; FEEDERS])
        requires
            (a as int) < (ASSETS as int),
            old(self)@[a as int].incarnation < u64::MAX,
        ensures
            replace_post(old(self)@, final(self)@, a as int, allowed@),
    {
        let i = a as usize;
        let st = self.assets[i];
        let c = st.cand;
        let ns = AssetState {
            incarnation: st.incarnation + 1,
            cand: [c[0] || allowed[0], c[1] || allowed[1], c[2] || allowed[2], c[3] || allowed[3]],
        };
        self.assets[i] = ns;
        assert forall|x: int| 0 <= x < FEEDERS as int implies #[trigger] self@[a as int].cand@[x] == (old(self)@[a as int].cand@[x] || allowed@[x]) by {
            assert(0 <= x < 4);
        }
    }

    /// Assumed-current truthful evidence: asset a (current incarnation) is on
    /// feeder f. Not authenticated here: signatures and chronology are not checked.
    pub fn prune(&mut self, a: u32, f: u8)
        requires
            (a as int) < (ASSETS as int),
            (f as int) < (FEEDERS as int),
        ensures
            prune_post(old(self)@, final(self)@, a as int, f as int),
    {
        let i = a as usize;
        let st = self.assets[i];
        let ns = AssetState {
            incarnation: st.incarnation,
            cand: [f == 0, f == 1, f == 2, f == 3],
        };
        self.assets[i] = ns;
        assert forall|x: int| 0 <= x < FEEDERS as int implies #[trigger] self@[a as int].cand@[x] == (x == f as int) by {
            assert(0 <= x < 4);
        }
    }
}

} // verus!
