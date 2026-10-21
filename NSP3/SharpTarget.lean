import NSP3.OrderedSimplex

namespace NSP3

/-- The integral ceiling of `n² / 4`, written without real numbers. -/
def quarterSquareCeil (n : ℕ) : ℕ :=
  (n * n + 3) / 4

/-- The ordered no-full-support target in terms of the three pair counts. -/
noncomputable def noFullTarget (S : CyclicStaircase) : ℕ :=
  quarterSquareCeil
    (pair12Count S.D + pair13Count S.D + pair23Count S.D + 1)

@[simp] theorem quarterSquareCeil_even (k : ℕ) :
    quarterSquareCeil (2 * k) = k * k := by
  unfold quarterSquareCeil
  have h : (2 * k) * (2 * k) + 3 = 4 * (k * k) + 3 := by ring
  rw [h]
  omega

@[simp] theorem quarterSquareCeil_odd (k : ℕ) :
    quarterSquareCeil (2 * k + 1) = k * k + k + 1 := by
  unfold quarterSquareCeil
  have h : (2 * k + 1) * (2 * k + 1) + 3 =
      4 * (k * k + k + 1) := by ring
  rw [h]
  omega

theorem noFullTarget_eq_square (S : CyclicStaircase) :
    noFullTarget S =
      ((pair12Count S.D + pair13Count S.D + pair23Count S.D + 1) ^ 2 + 3) / 4 := by
  simp [noFullTarget, quarterSquareCeil, pow_two]

end NSP3
