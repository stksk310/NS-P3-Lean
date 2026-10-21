import NSP3.P3Main

namespace NSP3

/-- The supremum in P3_MAIN is an actual greatest attained value of the full
numerical-semigroup spectrum, not just a bound for an explicit family. -/
theorem L12_P3_isGreatest (m : ℕ) (hm : 4 ≤ m) :
    IsGreatest (sharpRhoValues m)
      ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ := by
  exact all_m_rho_values_isGreatest m hm

end NSP3
