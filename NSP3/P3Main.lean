import NSP3.V03.Main

namespace NSP3

/-- Problem 3: the shifted index e=3 means actual embedding dimension four. -/
theorem P3_MAIN (m : ℕ) (hm : 4 ≤ m) :
    P3_R m = ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ := by
  exact V03.P3_MAIN_real m hm

end NSP3
