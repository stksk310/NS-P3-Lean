import NSP3.SymbolicThin23Sharp
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hs : 2 ≤ pair13Count S.D) (hy : g.y=1) (hz : g.z=1)
    (hne : pair13Count S.D < pair12Count S.D ∨ pair12Count S.D < g.x) :
    fullTarget S ≤ S.m :=
  fullSupport_t2_h11_nonbalanced_sharp S hg hf ho ht hs hy hz hne
end NSP3
