import NSP3.SharpnessAssembly

namespace NSP3

/-- The actual presentation-cardinality supremum of all cofinite edim-four
submonoids at multiplicity m. Its literature interpretation uses m >= 4. -/
noncomputable def P3_R (m : ℕ) : ℕ := sSup (sharpRhoValues m)

/-- Problem 3: the shifted index e=3 means actual embedding dimension four. -/
theorem P3_MAIN (m : ℕ) (hm : 4 ≤ m) :
    P3_R m = ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ := by
  exact all_m_rho_values_sSup m hm

end NSP3
