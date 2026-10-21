import NSP3.BoundarySharp

namespace NSP3

private theorem boundary_sqrt_scale (m : ℕ) :
    Real.sqrt ((4 * m : ℕ) : ℝ) = 2 * Real.sqrt (m : ℝ) := by
  push_cast
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

/-- Natural floor, including m=0; no interchange of floor and multiplication. -/
theorem boundary_real_floor_eq (m : ℕ) :
    ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ = 2 + Nat.sqrt (4 * m) := by
  rw [← boundary_sqrt_scale m, add_comm]
  change ⌊Real.sqrt ((4 * m : ℕ) : ℝ) + ((2 : ℕ) : ℝ)⌋₊ = 2 + Nat.sqrt (4 * m)
  rw [Nat.floor_add_natCast (Real.sqrt_nonneg _) 2,
    Real.nat_floor_real_sqrt_eq_nat_sqrt]
  omega

/-- Ordinary integer floor version of exactly the same paper expression. -/
theorem boundary_int_floor_eq (m : ℕ) :
    ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋ = (2 + Nat.sqrt (4 * m) : ℕ) := by
  rw [← boundary_sqrt_scale m]
  change ⌊((2 : ℕ) : ℝ) + Real.sqrt ((4 * m : ℕ) : ℝ)⌋ = (2 + Nat.sqrt (4 * m) : ℕ)
  rw [Int.floor_natCast_add 2, Real.floor_real_sqrt_eq_nat_sqrt]
  push_cast
  rfl

theorem cyclicStaircase_boundary_card_real_sharp (S : CyclicStaircase) :
    Nat.card {b : Point3 // MinimalComplement S.D b} ≤
      ⌊(2 : ℝ) + 2 * Real.sqrt (S.m : ℝ)⌋₊ := by
  rw [boundary_real_floor_eq]
  exact cyclicStaircase_boundary_card_sharp S

end NSP3
