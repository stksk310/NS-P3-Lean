import NSP3.SymbolicT2OneUnit
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hx : g.x=1) (hy : 2≤g.y) (hz : 2≤g.z) : fullTarget S≤S.m :=
  fullSupport_t2_x_unit_sharp S hg hf ho ht hx hy hz
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hr : pair12Count S.D=2) (hs : pair13Count S.D=2) : fullTarget S≤S.m :=
  fullSupport_t2_all_pair_two_sharp S hg hf ho ht hr hs
end NSP3
