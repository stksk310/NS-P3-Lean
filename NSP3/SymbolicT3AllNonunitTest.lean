import NSP3.SymbolicT3AllNonunit

namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hy : 2≤g.y) (hz : 2≤g.z) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      3*pair12Count S.D+g.x*g.y*g.z+g.y*g.z+2≤S.m :=
  fullSupport_t3_positive_box_yz_lower S hg hf ho ht hy hz

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : 6≤pair12Count S.D) (hx : 2≤g.x) (hy : 2≤g.y) (hz : 2≤g.z) :
    fullTarget S≤S.m := fullSupport_t3_no_unit_ge6_sharp S hg hf ho ht hr hx hy hz
end NSP3
