import NSP3.SymbolicT3UnitIntegration

namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : 2 ≤ g.x) (hz : g.z=1) : fullTarget S ≤ S.m :=
  fullSupport_t3_z_unit_or_h11_sharp S hg hf ho ht hx hz

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) :
    fullTarget S ≤ S.m ∨
      (2 ≤ g.x ∧ g.y=1 ∧ 2 ≤ g.z) ∨
      (g.x=1 ∧ 2 ≤ g.y ∧ 2 ≤ g.z) ∨
      (g.x=1 ∧ 2 ≤ g.y ∧ g.z=1) ∨
      (g.x=1 ∧ g.y=1 ∧ 2 ≤ g.z) :=
  fullSupport_t3_remaining_unit_cover S hg hf ho ht
end NSP3
