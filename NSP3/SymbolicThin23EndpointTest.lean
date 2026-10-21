import NSP3.SymbolicThin23Endpoint
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hr : pair12Count S.D=2) (hs : pair13Count S.D=2)
    (hx : g.x=2) (hy : g.y=1) (hz : g.z=1) :
    fullTarget S ≤ S.m :=
  fullSupport_t2_h11_endpoint_sharp S hg hf ho ht hr hs hx hy hz

-- A failing sharp bound must reach exactly the genuinely open balanced equality.
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hs : 2 ≤ pair13Count S.D) (hy : g.y=1) (hz : g.z=1)
    (hfail : S.m < fullTarget S) :
    pair12Count S.D=g.x ∧ pair13Count S.D=g.x ∧ 3 ≤ g.x ∧
      S.m=(g.x+1)*(g.x+3) :=
  thin23_failure_forces_balanced_equality S hg hf ho ht hs hy hz hfail
end NSP3
