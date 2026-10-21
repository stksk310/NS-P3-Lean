import NSP3.SymbolicT3R3Endpoint

namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hr : pair12Count S.D = 3)
    (hy : g.y = 1) (hz : g.z = 1) : fullTarget S ≤ S.m :=
  fullSupport_t3_h11_r3_sharp S hg hf ho ht hr hy hz
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hy : g.y = 1) (hz : g.z = 1) : fullTarget S ≤ S.m :=
  fullSupport_t3_h11_ordered_sharp S hg hf ho ht hy hz
end NSP3
