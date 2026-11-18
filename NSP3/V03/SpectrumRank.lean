import NSP3.V03.SpectrumFamilies
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace NSP3.V03

private def rationalTail (u : Fact4) : Fin 3 → ℚ := ![u.2.x,u.2.y,u.2.z]

private theorem rationalTail_add (u v : Fact4) :
    rationalTail (u+v)=rationalTail u+rationalTail v := by
  funext i
  fin_cases i <;> simp [rationalTail]

private noncomputable def relationTailSpan (R : Finset (Fact4 × Fact4)) :
    Submodule ℚ (Fin 3 → ℚ) :=
  Submodule.span ℚ ((R.image (fun e => rationalTail e.1-rationalTail e.2)) : Set (Fin 3 → ℚ))

private theorem presentationRel_tail_mem (R : Finset (Fact4 × Fact4))
    {u v : Fact4} (h : PresentationRel R u v) :
    rationalTail u-rationalTail v ∈ relationTailSpan R := by
  classical
  induction h with
  | edge he =>
    exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨_,he,rfl⟩))
  | refl u => simp
  | symm _ ih => simpa only [neg_sub] using (relationTailSpan R).neg_mem ih
  | trans _ _ ih₁ ih₂ =>
    convert (relationTailSpan R).add_mem ih₁ ih₂ using 1; abel
  | context _ d ih => simpa only [rationalTail_add, add_sub_add_right_eq_sub] using ih

/-- Three rationally independent tail directions are forced by the numerical kernel. -/
theorem factor_presentation_card_ge_three (m a b c : ℕ) (hm : 0 < m)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R) :
    3 ≤ R.card := by
  classical
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have h₀ : Pi.single (0 : Fin 3) (1 : ℚ) ∈ relationTailSpan R := by
    have hr : PresentationRel R (a,⟨0,0,0⟩) (0,⟨m,0,0⟩) :=
      (hR _ _).mpr (by simp [factorWeight, aperyWeight, mul_comm])
    have hc := (relationTailSpan R).smul_mem (-(m : ℚ)⁻¹) (presentationRel_tail_mem R hr)
    convert hc using 1
    funext i
    fin_cases i <;> simp [rationalTail, hmQ]
  have h₁ : Pi.single (1 : Fin 3) (1 : ℚ) ∈ relationTailSpan R := by
    have hr : PresentationRel R (b,⟨0,0,0⟩) (0,⟨0,m,0⟩) :=
      (hR _ _).mpr (by simp [factorWeight, aperyWeight, mul_comm])
    have hc := (relationTailSpan R).smul_mem (-(m : ℚ)⁻¹) (presentationRel_tail_mem R hr)
    convert hc using 1
    funext i
    fin_cases i <;> simp [rationalTail, hmQ]
  have h₂ : Pi.single (2 : Fin 3) (1 : ℚ) ∈ relationTailSpan R := by
    have hr : PresentationRel R (c,⟨0,0,0⟩) (0,⟨0,0,m⟩) :=
      (hR _ _).mpr (by simp [factorWeight, aperyWeight, mul_comm])
    have hc := (relationTailSpan R).smul_mem (-(m : ℚ)⁻¹) (presentationRel_tail_mem R hr)
    convert hc using 1
    funext i
    fin_cases i <;> simp [rationalTail, hmQ]
  have htop : relationTailSpan R=⊤ := by
    apply Submodule.eq_top_iff'.mpr
    intro v
    have hv := (relationTailSpan R).add_mem
      ((relationTailSpan R).add_mem ((relationTailSpan R).smul_mem (v 0) h₀)
        ((relationTailSpan R).smul_mem (v 1) h₁))
      ((relationTailSpan R).smul_mem (v 2) h₂)
    convert hv using 1
    funext i
    fin_cases i <;> simp
  have hc := finrank_span_finset_le_card (R := ℚ)
    (R.image (fun e => rationalTail e.1-rationalTail e.2))
  change Module.finrank ℚ (relationTailSpan R) ≤ _ at hc
  rw [htop] at hc
  have hthree : 3 ≤ (R.image (fun e => rationalTail e.1-rationalTail e.2)).card := by
    simpa using hc
  exact hthree.trans Finset.card_image_le

theorem intrinsicRho_ge_three (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    3 ≤ intrinsicRho (generatedSemigroup m a b c) := by
  rw [literature_rho_identification m a b c h]
  obtain ⟨R,hR,hcard⟩ := minimumFourInputRelations_attained m a b c h.positive h.coprime
  rw [← hcard]
  exact factor_presentation_card_ge_three m a b c h.positive R hR

theorem spectrum_member_ge_three {m q : ℕ} (hq : q ∈ NSP3.sharpRhoValues m) : 3 ≤ q := by
  rcases hq with ⟨S,hcof,hedim,hmult,hrho⟩
  obtain ⟨a,b,c,h,heq⟩ := numerical_semigroup_class_coverage S m hcof hedim hmult
  have hset : generatedSemigroup m a b c = (S : Set ℕ) :=
    congrArg (fun T : AddSubmonoid ℕ => (T : Set ℕ)) heq
  rw [← hrho]
  simpa only [hset] using intrinsicRho_ge_three m a b c h

end NSP3.V03
