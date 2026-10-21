import NSP3.SymbolicT3UnitSharp
import NSP3.SymbolicT3R3Endpoint

namespace NSP3

/-- The old h11 theorem and the new z-unit theorem cover every y at x≥2,z=1. -/
theorem fullSupport_t3_z_unit_or_h11_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : 2 ≤ g.x) (hz : g.z=1) : fullTarget S ≤ S.m := by
  by_cases hy : g.y=1
  · exact fullSupport_t3_h11_ordered_sharp S hg hf ho ht hy hz
  · exact fullSupport_t3_one_unit_z_symbolic_sharp S hg hf ho ht hz hx (by have := hf.2.1;omega)

/-- Exhaustive residual ledger: a sharp conclusion or one of four genuinely open orientations.
This theorem is not a proof of the general ordered t3 sharp bound. -/
theorem fullSupport_t3_remaining_unit_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) :
    fullTarget S ≤ S.m ∨
      (2 ≤ g.x ∧ g.y=1 ∧ 2 ≤ g.z) ∨
      (g.x=1 ∧ 2 ≤ g.y ∧ 2 ≤ g.z) ∨
      (g.x=1 ∧ 2 ≤ g.y ∧ g.z=1) ∨
      (g.x=1 ∧ g.y=1 ∧ 2 ≤ g.z) := by
  rcases fullSupport_t3_unit_partition S hg hf ho ht with
    hnon | hh11 | h1h1 | h11h | hxy1 | hx1z | h1yz
  · exact Or.inl (fullSupport_t3_nonunit_ordered_sharp S hg hf ho ht hnon.1 hnon.2.1 hnon.2.2)
  · exact Or.inl (fullSupport_t3_z_unit_or_h11_sharp S hg hf ho ht hh11.1 hh11.2.2)
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h11h)))
  · exact Or.inl (fullSupport_t3_z_unit_or_h11_sharp S hg hf ho ht hxy1.1 hxy1.2.2)
  · exact Or.inr (Or.inl hx1z)
  · exact Or.inr (Or.inr (Or.inl h1yz))

end NSP3
