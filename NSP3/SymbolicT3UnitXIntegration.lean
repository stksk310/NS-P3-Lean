import NSP3.SymbolicT3UnitXEndpoint
import NSP3.SymbolicT3UnitYIntegration

namespace NSP3

/-- All ordered t3 configurations except the two remaining x-unit axes. -/
theorem fullSupport_t3_x_or_yz_nonunit_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hu : 2 ≤ g.x ∨ (2 ≤ g.y ∧ 2 ≤ g.z)) :
    fullTarget S ≤ S.m := by
  rcases hu with hx | ⟨hy,hz⟩
  · exact fullSupport_t3_x_nonunit_symbolic_sharp S hg hf ho ht hx
  · by_cases hx : 2 ≤ g.x
    · exact fullSupport_t3_x_nonunit_symbolic_sharp S hg hf ho ht hx
    · exact fullSupport_t3_one_unit_x_symbolic_sharp S hg hf ho ht
        (by have := hf.1; omega) hy hz

/-- A residual disjunction, explicitly not a universal ordered sharp theorem. -/
theorem fullSupport_t3_remaining_two_unit_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) :
    fullTarget S ≤ S.m ∨ (g.x=1 ∧ 2 ≤ g.y ∧ g.z=1) ∨
      (g.x=1 ∧ g.y=1 ∧ 2 ≤ g.z) := by
  rcases fullSupport_t3_remaining_x_unit_cover S hg hf ho ht with
    hdone | ⟨hx,hy,hz,_⟩ | h1h1 | h11h
  · exact Or.inl hdone
  · exact Or.inl (fullSupport_t3_one_unit_x_symbolic_sharp S hg hf ho ht hx hy hz)
  · exact Or.inr (Or.inl h1h1)
  · exact Or.inr (Or.inr h11h)

end NSP3
