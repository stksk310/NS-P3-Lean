import NSP3.SymbolicT3NonunitCoverage

namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hr : pair12Count S.D = 3)
    (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    fullTarget S ≤ S.m ∨ g=Point3.mk 2 2 2 :=
  fullSupport_t3_nonunit_r3_cover S hg hf ho ht hr hx hy hz
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hr : pair12Count S.D = 4)
    (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    fullTarget S ≤ S.m ∨ (pair13Count S.D=4 ∧ g=Point3.mk 3 2 2) :=
  fullSupport_t3_nonunit_r4_cover S hg hf ho ht hr hx hy hz
end NSP3
