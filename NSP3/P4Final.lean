import NSP3.MacaulayC3
import NSP3.P3Main

namespace NSP3

theorem P3_R_nat_sqrt (m : ℕ) (hm : 4 ≤ m) :
    P3_R m = 2 + Nat.sqrt (4 * m) := by
  rw [P3_MAIN m hm, boundary_real_floor_eq]

/-- The finite equality interval is computed from the actual Macaulay definition. -/
theorem P4_small_eq (m : ℕ) (hm : 4 ≤ m) (hu : m ≤ 9) :
    P3_R m = C3 m := by
  rw [P3_R_nat_sqrt m hm]
  interval_cases m <;> norm_num <;> decide

/-- The finite exceptional strict interval, with no change to the definition. -/
theorem P4_middle_strict (m : ℕ) (hl : 10 ≤ m) (hu : m ≤ 19) :
    P3_R m < C3 m := by
  rw [P3_R_nat_sqrt m (by omega)]
  interval_cases m <;> norm_num <;> decide

/-- All remaining multiplicities use the symbolic arbitrary-degree inequality. -/
theorem P4_large_strict (m : ℕ) (hm : 20 ≤ m) :
    P3_R m < C3 m := by
  rw [P3_R_nat_sqrt m (by omega)]
  exact lt_of_lt_of_le
    (sqrt_bound_lt_binomial (c3Degree m) m (c3Degree_ge_four m hm)
      (c3Degree_interval m (by omega)).2)
    (C3_ge_binomial m (by omega))

theorem P4_strict (m : ℕ) (hm : 10 ≤ m) : P3_R m < C3 m := by
  by_cases h : m ≤ 19
  · exact P4_middle_strict m hm h
  · exact P4_large_strict m (by omega)

/-- Problem 4 at shifted index e=3, hence actual embedding dimension four. -/
theorem P4_e3 (m : ℕ) (hm : 4 ≤ m) :
    P3_R m = C3 m ↔ m ≤ 9 := by
  constructor
  · intro he
    by_contra hn
    have hlt := P4_strict m (by omega)
    omega
  · exact P4_small_eq m hm

end NSP3
