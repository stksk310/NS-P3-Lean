import NSP3.SymbolicT3UnitEndpoint

namespace NSP3

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hz : g.z=1)
    (he : (pair12Count S.D=4 ∧ pair13Count S.D=3 ∧ g.x=2 ∧ g.y=3) ∨
      (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ g.x=3 ∧ g.y=2) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ g.x=4 ∧ g.y=2) ∨
      (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ g.x=2 ∧ g.y=3)) :
    fullTarget S ≤ S.m := fullSupport_t3_unit_z_small_BF_sharp S hg hf ho ht hz he

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=2) (hy : g.y=2) (hz : g.z=1) : 30 ≤ S.m :=
  fullSupport_t3_unit_z_r3_BF_lower S hg hf ho ht hr hx hy hz

end NSP3
