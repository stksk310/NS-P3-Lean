import NSP3.SharpTarget

namespace NSP3

theorem simplexCard_succ_succ (s n : ℕ) :
    simplexCard s (n + 2) =
      simplexCard s (n + 1) + (n + 1) * (s - (n + 1)) := by
  simp [simplexCard, Finset.sum_range_succ, Nat.add_comm]

theorem six_mul_simplexCard (s t : ℕ) (hst : t ≤ s) :
    6 * simplexCard s t = t * (t - 1) * (3 * s - 2 * t + 1) := by
  induction t using Nat.twoStepInduction with
  | zero => simp [simplexCard]
  | one => simp [simplexCard]
  | more n ih0 ih1 =>
      have hn1 : n + 1 ≤ s := by omega
      have ih := ih1 hn1
      rw [simplexCard_succ_succ, Nat.mul_add, ih]
      let d := s - (n + 2)
      have hsrepr : s = d + (n + 2) := by
        dsimp [d]
        omega
      have hsm : s - (n + 1) = d + 1 := by
        dsimp [d]
        omega
      have hfac1 : 3 * s - 2 * (n + 1) + 1 = n + 3 * d + 5 := by
        dsimp [d]
        omega
      have hfac2 : 3 * s - 2 * (n + 2) + 1 = n + 3 * d + 3 := by
        dsimp [d]
        omega
      have hnsub1 : n + 1 - 1 = n := by omega
      have hnsub2 : n + 2 - 1 = n + 1 := by omega
      rw [hsm, hfac1, hfac2, hnsub1, hnsub2]
      ring

end NSP3
