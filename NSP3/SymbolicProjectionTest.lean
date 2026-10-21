import NSP3.SymbolicProjection

namespace NSP3
-- Break caught: replacing actual projection membership by triangular membership,
-- or adding an unproved global sharp/coverage hypothesis.
example (S : CyclicStaircase) {g p : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (hp : FullSupport p) (h12 : proj12 p ∈ S.D)
    (h13 : proj13 p ∈ S.D) (h23 : proj23 p ∈ S.D) (havoid : ¬ g ≤ p) :
    p ∈ S.D := fullSupport_actual_projection_lifting S hg hf hp h12 h13 h23 havoid
end NSP3
