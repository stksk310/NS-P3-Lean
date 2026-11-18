import NSP3.P3Main

namespace NSP3

theorem P3_R_nat_sqrt (m : ℕ) (hm : 4 ≤ m) :
    P3_R m = 2 + Nat.sqrt (4 * m) := by
  simpa only [V03.T] using V03.P3_MAIN m hm

/-- The finite equality interval is computed from the actual Macaulay definition. -/
theorem P4_small_eq (m : ℕ) (hm : 4 ≤ m) (hu : m ≤ 9) :
    P3_R m = C3 m := by
  rw [P3_R_nat_sqrt m hm]
  exact V03.macaulay_small m hm hu

/-- The finite exceptional strict interval, with no change to the definition. -/
theorem P4_middle_strict (m : ℕ) (hl : 10 ≤ m) (hu : m ≤ 19) :
    P3_R m < C3 m := by
  rw [P3_R_nat_sqrt m (by omega)]
  exact V03.macaulay_middle m hl hu

/-- All remaining multiplicities use V03's short binomial comparison. -/
theorem P4_large_strict (m : ℕ) (hm : 20 ≤ m) :
    P3_R m < C3 m := by
  rw [P3_R_nat_sqrt m (by omega)]
  exact V03.macaulay_large m hm

theorem P4_strict (m : ℕ) (hm : 10 ≤ m) : P3_R m < C3 m := by
  rw [P3_R_nat_sqrt m (by omega)]
  exact V03.macaulay_strict m hm

/-- Problem 4 at shifted index e=3, hence actual embedding dimension four. -/
theorem P4_e3 (m : ℕ) (hm : 4 ≤ m) :
    P3_R m = C3 m ↔ m ≤ 9 := by
  exact V03.P4_e3 m hm

end NSP3
