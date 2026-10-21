import NSP3.SymbolicThin23Balanced
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hr : pair12Count S.D=g.x) (hs : pair13Count S.D=g.x)
    (hk : 3 ≤ g.x) (hy : g.y=1) (hz : g.z=1)
    (hm : S.m=(g.x+1)*(g.x+3)) : False :=
  fullSupport_t2_h11_balanced_equality_impossible S hg hf ho ht hr hs hk hy hz hm
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hs : 2 ≤ pair13Count S.D) (hy : g.y=1) (hz : g.z=1) :
    fullTarget S ≤ S.m := fullSupport_t2_h11_sharp S hg hf ho ht hs hy hz
end NSP3
