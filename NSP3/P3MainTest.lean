import NSP3.P3Main

example (m : ℕ) (hm : 4 ≤ m) :
    NSP3.P3_R m = ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ :=
  NSP3.P3_MAIN m hm

example (m : ℕ) : NSP3.P3_R m = sSup (NSP3.sharpRhoValues m) := rfl

example (m : ℕ) (hm : 4 ≤ m) : NSP3.P3_R m = 2 + Nat.sqrt (4*m) := by
  rw [NSP3.P3_MAIN m hm, NSP3.boundary_real_floor_eq]

example : NSP3.P3_R 4 = 6 := by
  rw [NSP3.P3_MAIN 4 (by omega), NSP3.boundary_real_floor_eq]
  norm_num

example : NSP3.P3_R 9 = 8 := by
  rw [NSP3.P3_MAIN 9 (by omega), NSP3.boundary_real_floor_eq]
  norm_num
