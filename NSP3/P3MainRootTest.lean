import NSP3.Main

-- NSP3.Main is the sole import of the frozen root Main.lean entry point.
#check NSP3.P3_R
#check NSP3.P3_MAIN
#check NSP3.L12_P3_isGreatest

example (m : ℕ) (hm : 4 ≤ m) :
    NSP3.P3_R m = ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ :=
  NSP3.P3_MAIN m hm

example (m : ℕ) (hm : 4 ≤ m) :
    IsGreatest (NSP3.sharpRhoValues m)
      ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ :=
  NSP3.L12_P3_isGreatest m hm
