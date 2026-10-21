import NSP3.SymbolicT3Balanced
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (he : pair12Count S.D=pair13Count S.D) (hk : 4≤pair12Count S.D)
    (hh : pair12Count S.D≤g.x) (hy : g.y=1) (hz : g.z=1) : fullTarget S≤S.m :=
  fullSupport_t3_balanced_h11_sharp S hg hf ho ht he hk hh hy hz
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (he : pair12Count S.D=pair13Count S.D) (hk : pair12Count S.D=4)
    (hh : g.x=4) (hy : g.y=1) (hz : g.z=1)
    (h13 : Point3.mk 0 1 3∈S.D) (h31 : Point3.mk 0 3 1∈S.D)
    (hm : S.m≤42) : False :=
  t3_balanced_k4_present_no_go S hg hf ho ht he hk hh hy hz h13 h31 hm
/-- The modular equations alone permit nonzero nonunit coefficients; the actual
standard-point injectivity in the production proof is indispensable. -/
example : (21:ZMod 42)≠0 ∧ 5*(21:ZMod 42)+21=4*21 ∧
    4*(21:ZMod 42)+21+21=0 ∧ 2*(21:ZMod 42)=0 := by decide
end NSP3
