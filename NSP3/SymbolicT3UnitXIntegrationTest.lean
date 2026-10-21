import NSP3.SymbolicT3UnitXIntegration

namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hu : 2 ≤ g.x ∨ (2 ≤ g.y ∧ 2 ≤ g.z)) :
    fullTarget S ≤ S.m := fullSupport_t3_x_or_yz_nonunit_sharp S hg hf ho ht hu

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) :
    fullTarget S ≤ S.m ∨ (g.x=1 ∧ 2 ≤ g.y ∧ g.z=1) ∨
      (g.x=1 ∧ g.y=1 ∧ 2 ≤ g.z) :=
  fullSupport_t3_remaining_two_unit_cover S hg hf ho ht
end NSP3
