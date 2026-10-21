import NSP3.BoundaryReal

namespace NSP3.Sharpness

/-- The exact natural-valued sharp target, including non-square multiplicities. -/
def sharpTarget (m : ℕ) : ℕ := 2 + Nat.sqrt (4 * m)

/-- Reuse the frozen real-floor bridge without commuting multiplication and floor. -/
theorem sharpTarget_eq_real_floor (m : ℕ) :
    sharpTarget m = ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ :=
  (boundary_real_floor_eq m).symm

/-- The admissible multiplicity range gives the construction's minimum target. -/
theorem sharpTarget_ge_six {m : ℕ} (hm : 4 ≤ m) : 6 ≤ sharpTarget m := by
  have hn : 4 ≤ Nat.sqrt (4 * m) := Nat.le_sqrt.mpr (by omega)
  unfold sharpTarget
  omega

/-- Every admissible multiplicity selects one of the two explicit construction ranges. -/
theorem sharpTarget_parameter_split {m : ℕ} (hm : 4 ≤ m) :
    (∃ k, 1 ≤ k ∧ sharpTarget m = 2*k+4 ∧ (k+1)^2 ≤ m) ∨
    (∃ k, 2 ≤ k ∧ sharpTarget m = 2*k+3 ∧ k*k+k+1 ≤ m) := by
  have hn : 4 ≤ Nat.sqrt (4 * m) := Nat.le_sqrt.mpr (by omega)
  have hs := Nat.sqrt_le' (4 * m)
  by_cases he : Nat.sqrt (4 * m) % 2 = 0
  · let k := (Nat.sqrt (4 * m) - 2) / 2
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hn_eq : Nat.sqrt (4 * m) = 2*k+2 := by dsimp [k]; omega
    left
    refine ⟨k, hk, ?_, ?_⟩
    · unfold sharpTarget
      omega
    · rw [hn_eq] at hs
      nlinarith
  · let k := (Nat.sqrt (4 * m) - 1) / 2
    have hk : 2 ≤ k := by dsimp [k]; omega
    have hn_eq : Nat.sqrt (4 * m) = 2*k+1 := by dsimp [k]; omega
    right
    refine ⟨k, hk, ?_, ?_⟩
    · unfold sharpTarget
      omega
    · rw [hn_eq] at hs
      nlinarith

/-- The same selection theorem stated in the final attainment theorem's notation. -/
theorem real_floor_parameter_split {m : ℕ} (hm : 4 ≤ m) :
    (∃ k, 1 ≤ k ∧ ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ = 2*k+4 ∧
      (k+1)^2 ≤ m) ∨
    (∃ k, 2 ≤ k ∧ ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ = 2*k+3 ∧
      k*k+k+1 ≤ m) := by
  simpa only [← sharpTarget_eq_real_floor] using sharpTarget_parameter_split hm

end NSP3.Sharpness
