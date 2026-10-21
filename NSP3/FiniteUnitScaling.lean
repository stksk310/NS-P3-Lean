import NSP3.FiniteSeedFilters
import Mathlib.Data.ZMod.Units

namespace NSP3

def scaleResidueWeights {m : ℕ} (u : (ZMod m)ˣ)
    (w : ResidueWeights m) : ResidueWeights m :=
  ⟨(u : ZMod m)*w.p1, (u : ZMod m)*w.p2, (u : ZMod m)*w.p3⟩

@[simp] theorem residueWithWeights_unit_scale {m : ℕ} (u : (ZMod m)ˣ)
    (w : ResidueWeights m) (p : Point3) :
    residueWithWeights (scaleResidueWeights u w) p =
      (u : ZMod m) * residueWithWeights w p := by
  simp only [scaleResidueWeights, residueWithWeights, residueOf]
  ring

theorem unit_mul_injective {m : ℕ} (u : (ZMod m)ˣ) :
    Function.Injective (fun a : ZMod m => (u : ZMod m)*a) := by
  intro a b h
  have := congrArg (fun c => (↑(u⁻¹) : ZMod m)*c) h
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using this

@[simp] theorem residue_eq_unit_scale_iff {m : ℕ} (u : (ZMod m)ˣ)
    (w : ResidueWeights m) (p a : Point3) :
    residueWithWeights (scaleResidueWeights u w) p =
      residueWithWeights (scaleResidueWeights u w) a ↔
    residueWithWeights w p = residueWithWeights w a := by
  simp only [residueWithWeights_unit_scale]
  exact (unit_mul_injective u).eq_iff

@[simp] theorem residue_zero_unit_scale_iff {m : ℕ} (u : (ZMod m)ˣ)
    (w : ResidueWeights m) (p : Point3) :
    residueWithWeights (scaleResidueWeights u w) p = 0 ↔
      residueWithWeights w p = 0 := by
  simp only [residueWithWeights_unit_scale]
  simpa only [mul_zero] using
    ((unit_mul_injective u).eq_iff (a := residueWithWeights w p) (b := 0))

@[simp] theorem residueInjectiveOn_unit_scale_iff {m : ℕ} (u : (ZMod m)ˣ)
    (w : ResidueWeights m) (A : Finset Point3) :
    residueInjectiveOn A (scaleResidueWeights u w) ↔ residueInjectiveOn A w := by
  classical
  simp only [residueInjectiveOn, Finset.card_image_iff, Set.InjOn]
  simp only [residue_eq_unit_scale_iff]

@[simp] theorem residue_fresh_unit_scale_iff {m : ℕ} (u : (ZMod m)ˣ)
    (w : ResidueWeights m) (A : Finset Point3) (p : Point3) :
    residueWithWeights (scaleResidueWeights u w) p ∉
      A.image (residueWithWeights (scaleResidueWeights u w)) ↔
    residueWithWeights w p ∉ A.image (residueWithWeights w) := by
  simp only [Finset.mem_image, residue_eq_unit_scale_iff]

theorem extensionCandidates_unit_scale {m : ℕ} (u : (ZMod m)ˣ)
    (w : ResidueWeights m) (n : ℕ) (A : Finset Point3) :
    extensionCandidates n (scaleResidueWeights u w) A = extensionCandidates n w A := by
  ext p
  simp only [mem_extensionCandidates, residue_fresh_unit_scale_iff]

theorem downsetCompletions_unit_scale {m : ℕ} (u : (ZMod m)ˣ)
    (w : ResidueWeights m) (fuel n : ℕ) (A : Finset Point3) :
    downsetCompletions fuel n (scaleResidueWeights u w) A =
      downsetCompletions fuel n w A := by
  induction fuel generalizing A with
  | zero => rfl
  | succ fuel ih =>
      simp only [downsetCompletions, extensionCandidates_unit_scale, ih]

/-- Nonunits remain legal: every nonzero first coefficient scales to a proper
positive divisor of the modulus, using Mathlib's complete associate theorem. -/
theorem exists_divisor_normalization {m : ℕ} [NeZero m]
    (w : ResidueWeights m) (h : w.p1 ≠ 0) :
    ∃ (u : (ZMod m)ˣ) (d : ℕ), d ∣ m ∧ 0 < d ∧ d < m ∧
      (scaleResidueWeights u w).p1 = (d : ZMod m) := by
  obtain ⟨d, hd, a, ha, heq⟩ := ZMod.eq_unit_mul_divisor w.p1
  obtain ⟨v, hv⟩ := ha
  have hdz : d ≠ 0 := by
    intro hz
    apply h
    simp [heq, hz]
  have hdm : d ≠ m := by
    intro hm
    apply h
    simp [heq, hm]
  refine ⟨v⁻¹, d, hd, Nat.pos_of_ne_zero hdz,
    lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) hd) hdm, ?_⟩
  change (↑(v⁻¹) : ZMod m)*w.p1 = _
  rw [heq, ← hv, ← mul_assoc, Units.inv_mul, one_mul]

end NSP3
