import NSP3.SharpnessParameters
namespace NSP3.Sharpness
-- Removing the parameter-selection API must make these universal contract tests fail.
example (m : ℕ) : sharpTarget m = ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ :=
  sharpTarget_eq_real_floor m
example (m : ℕ) (hm : 4 ≤ m) : 6 ≤ sharpTarget m := sharpTarget_ge_six hm
example (m : ℕ) (hm : 4 ≤ m) :
    (∃ k, 1 ≤ k ∧ sharpTarget m = 2*k+4 ∧ (k+1)^2 ≤ m) ∨
    (∃ k, 2 ≤ k ∧ sharpTarget m = 2*k+3 ∧ k*k+k+1 ≤ m) :=
  sharpTarget_parameter_split hm
end NSP3.Sharpness

namespace NSP3.Sharpness

example (m : ℕ) (hm : 4 ≤ m) :
    (∃ k, 1 ≤ k ∧ ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ = 2*k+4 ∧
      (k+1)^2 ≤ m) ∨
    (∃ k, 2 ≤ k ∧ ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ = 2*k+3 ∧
      k*k+k+1 ≤ m) := real_floor_parameter_split hm

-- Smallest multiplicities and the first parity transitions.
example : sharpTarget 4 = 6 := by norm_num [sharpTarget]
example : sharpTarget 5 = 6 := by norm_num [sharpTarget]
example : sharpTarget 6 = 6 := by norm_num [sharpTarget]
example : sharpTarget 7 = 7 := by norm_num [sharpTarget]
example : sharpTarget 8 = 7 := by norm_num [sharpTarget]
example : sharpTarget 9 = 8 := by norm_num [sharpTarget]

-- Universal square boundary fixes the even construction threshold.
example (k : ℕ) : sharpTarget ((k+1)^2) = 2*k+4 := by
  unfold sharpTarget
  have h : 4*((k+1)^2) = (2*(k+1))^2 := by ring
  rw [h, Nat.sqrt_eq']
  omega

-- Universal odd threshold, rather than a finite numerical sample.
example (k : ℕ) (hk : 2 ≤ k) : sharpTarget (k*k+k+1) = 2*k+3 := by
  have h : 2*k+1 = Nat.sqrt (4*(k*k+k+1)) :=
    Nat.eq_sqrt'.mpr ⟨by nlinarith, by nlinarith⟩
  unfold sharpTarget
  omega

#print axioms sharpTarget_eq_real_floor
#print axioms sharpTarget_ge_six
#print axioms sharpTarget_parameter_split
#print axioms real_floor_parameter_split

end NSP3.Sharpness
