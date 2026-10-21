import NSP3.SymbolicT3TwoUnitEndpoint
import NSP3.SymbolicT3UnitXIntegration

namespace NSP3

/-- Every legitimate ordered full-support t=3 boundary; no coordinate restriction. -/
theorem fullSupport_t3_ordered_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) : fullTarget S ≤ S.m := by
  rcases fullSupport_t3_remaining_two_unit_cover S hg hf ho ht with
    h | ⟨hx,hy,hz⟩ | ⟨hx,hy,hz⟩
  · exact h
  · exact fullSupport_t3_two_unit_x_symbolic_sharp S hg hf ho ht hx (Or.inr hz)
  · exact fullSupport_t3_two_unit_x_symbolic_sharp S hg hf ho ht hx (Or.inl hy)

end NSP3
