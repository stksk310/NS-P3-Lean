import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

namespace NSP3

/-- Rank-cut cost; all subtraction is truncated Nat subtraction as in the prose. -/
def rankCutCost (r A B l : ℕ) : ℕ :=
  (r-l)*(A-l) + l*(B+l-r) + (A-l)*(B+l-r)

def rankCutPhi (r A B : ℕ) : ℕ :=
  (Finset.range (r+1)).inf' (by simp) (rankCutCost r A B)

theorem rankCutPhi_le_cost {r A B l : ℕ} (hl : l ≤ r) :
    rankCutPhi r A B ≤ rankCutCost r A B l := by
  exact Finset.inf'_le _ (by simp; omega)

theorem le_rankCutPhi {r A B n : ℕ}
    (h : ∀ l, l ≤ r → n ≤ rankCutCost r A B l) : n ≤ rankCutPhi r A B := by
  apply Finset.le_inf'
  intro l hl
  exact h l (by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hl)))

/-- Pure arithmetic diagonal identity; not yet the actual plane-cardinality adapter. -/
theorem rankCutPhi_first_diagonal {r A B : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hdiag : A+B=r+1) :
    rankCutPhi r A B = min A B := by
  apply Nat.le_antisymm
  · have hleft := rankCutPhi_le_cost (A := A) (B := B)
      (l := A-1) (r := r) (by omega)
    have hright := rankCutPhi_le_cost (A := A) (B := B)
      (l := A) (r := r) (by omega)
    have he1 : rankCutCost r A B (A-1) = B := by
      have ha : A-(A-1)=1 := by omega
      have hb : B+(A-1)-r=0 := by omega
      have hr : r-(A-1)=B := by omega
      simp [rankCutCost, ha, hb, hr]
    have he2 : rankCutCost r A B A = A := by
      have hb : B+A-r=1 := by omega
      simp [rankCutCost, hb]
    rw [he1] at hleft
    rw [he2] at hright
    exact le_min hright hleft
  · apply le_rankCutPhi
    intro l hl
    by_cases hla : l < A
    · have hb : B+l-r=0 := by omega
      have ha : 1 ≤ A-l := by omega
      have hr : B ≤ r-l := by omega
      have hm := Nat.mul_le_mul hr ha
      simp only [rankCutCost, hb, mul_zero, add_zero]
      exact le_trans (min_le_right A B) (by simpa using hm)
    · have ha : A-l=0 := by omega
      have hb : 1 ≤ B+l-r := by omega
      have hm := Nat.mul_le_mul (show A ≤ l by omega) hb
      simp only [rankCutCost, ha, mul_zero, zero_mul, zero_add, add_zero]
      exact le_trans (min_le_left A B) (by simpa using hm)

end NSP3
