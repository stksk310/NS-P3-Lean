import NSP3.BoundaryReal

namespace NSP3

-- Break caught: treating floor(2+2 sqrt m) as 2+2 floor(sqrt m).
example (m : ℕ) : ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ = 2 + Nat.sqrt (4*m) :=
  boundary_real_floor_eq m

example (m : ℕ) : ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋ = (2 + Nat.sqrt (4*m) : ℕ) :=
  boundary_int_floor_eq m

example (S : CyclicStaircase) :
    Nat.card {b : Point3 // MinimalComplement S.D b} ≤
      ⌊(2 : ℝ) + 2 * Real.sqrt (S.m : ℝ)⌋₊ :=
  cyclicStaircase_boundary_card_real_sharp S

end NSP3
