import NSP3.BalancedArithmetic

namespace NSP3

example (R t : ℕ) (ht : 2 ≤ t) (htr : t ≤ R) :
    quarterSquareCeil (R + R + t + 1) ≤
      3 * R + 1 + Nat.choose R 2 + Nat.choose R 2 + Nat.choose t 2
        + simplexCard R t + 2 :=
  balancedTarget_le_m5_simplex_plus_two R t ht htr

example (R : ℕ) :
    quarterSquareCeil (R + R + 0 + 1) ≤
      3 * R + 1 + Nat.choose R 2 + Nat.choose R 2 + Nat.choose 0 2 :=
  balancedTarget_le_m5_t0 R

example (R : ℕ) :
    quarterSquareCeil (R + R + 1 + 1) ≤
      3 * R + 1 + Nat.choose R 2 + Nat.choose R 2 + Nat.choose 1 2 :=
  balancedTarget_le_m5_t1 R

example : quarterSquareCeil (2 + 2 + 2 + 1) ≤
    3 * 2 + 1 + Nat.choose 2 2 + Nat.choose 2 2 + Nat.choose 2 2
      + simplexCard 2 2 + 2 := by
  decide

example : quarterSquareCeil (3 + 3 + 3 + 1) ≤
    3 * 3 + 1 + Nat.choose 3 2 + Nat.choose 3 2 + Nat.choose 3 2
      + simplexCard 3 3 + 2 := by
  decide

example : quarterSquareCeil (4 + 4 + 4 + 1) ≤
    3 * 4 + 1 + Nat.choose 4 2 + Nat.choose 4 2 + Nat.choose 4 2
      + simplexCard 4 4 + 2 := by
  decide

end NSP3
