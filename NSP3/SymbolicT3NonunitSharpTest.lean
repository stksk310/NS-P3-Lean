import NSP3.SymbolicT3NonunitSharp

namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    fullTarget S ≤ S.m :=
  fullSupport_t3_nonunit_ordered_sharp S hg hf ho ht hx hy hz
end NSP3
