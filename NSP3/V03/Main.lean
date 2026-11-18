import NSP3.V03.Boundary
import NSP3.V03.Macaulay
import NSP3.P3Definition

namespace NSP3.V03

/-- V03's T(m), on the same natural-number convention as the public project. -/
def T (m : ℕ) : ℕ := 2+Nat.sqrt (4*m)

theorem numerical_semigroup_rho_upper (S : AddSubmonoid ℕ) (m : ℕ)
    (hcof : ((S : Set ℕ)ᶜ).Finite)
    (hedim : semigroupEmbeddingDimension (S : Set ℕ)=4)
    (hm : IsSemigroupMultiplicity (S : Set ℕ) m) :
    intrinsicRho (S : Set ℕ) ≤ T m := by
  obtain ⟨a,b,c,h,heq⟩ := numerical_semigroup_class_coverage S m hcof hedim hm
  have hset : generatedSemigroup m a b c=(S : Set ℕ) :=
    congrArg (fun U : AddSubmonoid ℕ => (U : Set ℕ)) heq
  simpa only [hset,T] using intrinsic_rho_sharp m a b c h

/-- Attainment uses unchanged actual numerical-semigroup constructions,
but its upper half follows the V03 capacity route. -/
theorem sharp_attainment (m : ℕ) (hm : 4 ≤ m) : T m ∈ sharpRhoValues m := by
  rcases Sharpness.real_floor_parameter_split hm with ⟨k,hk,heta,hbound⟩ | ⟨k,hk,heta,hbound⟩
  · have h := Sharpness.even_minimalFour m k hk hbound
    have hs := minimal_generator_class_bridge m (Sharpness.evenA m k)
      (Sharpness.evenB m k) (Sharpness.evenC m k) h
    refine ⟨generatedAddSubmonoid m (Sharpness.evenA m k) (Sharpness.evenB m k)
      (Sharpness.evenC m k),hs.2.2.2,hs.2.2.1,hs.1,?_⟩
    change intrinsicRho (generatedSemigroup m (Sharpness.evenA m k)
      (Sharpness.evenB m k) (Sharpness.evenC m k))=T m
    apply le_antisymm (intrinsic_rho_sharp _ _ _ _ h)
    have he : T m=2*k+4 := by simpa only [T,boundary_real_floor_eq] using heta
    unfold T at he
    rw [he]
    exact Sharpness.even_family_rho_lower m k hk hbound
  · have h := Sharpness.odd_minimalFour m k hk hbound
    have hs := minimal_generator_class_bridge m (Sharpness.oddA m k)
      (Sharpness.oddB m k) (Sharpness.oddC m k) h
    refine ⟨generatedAddSubmonoid m (Sharpness.oddA m k) (Sharpness.oddB m k)
      (Sharpness.oddC m k),hs.2.2.2,hs.2.2.1,hs.1,?_⟩
    change intrinsicRho (generatedSemigroup m (Sharpness.oddA m k)
      (Sharpness.oddB m k) (Sharpness.oddC m k))=T m
    apply le_antisymm (intrinsic_rho_sharp _ _ _ _ h)
    have he : T m=2*k+3 := by simpa only [T,boundary_real_floor_eq] using heta
    unfold T at he
    rw [he]
    exact Sharpness.odd_family_rho_lower m k hk hbound

theorem rho_values_isGreatest (m : ℕ) (hm : 4 ≤ m) :
    IsGreatest (sharpRhoValues m) (T m) := by
  refine ⟨sharp_attainment m hm,?_⟩
  rintro r ⟨S,hcof,hedim,hmult,hr⟩
  rw [← hr]
  exact numerical_semigroup_rho_upper S m hcof hedim hmult

/-- P3, on the original intrinsic presentation invariant and supremum definition. -/
theorem P3_MAIN (m : ℕ) (hm : 4 ≤ m) : NSP3.P3_R m=T m :=
  (rho_values_isGreatest m hm).csSup_eq

theorem P3_MAIN_real (m : ℕ) (hm : 4 ≤ m) :
    NSP3.P3_R m=⌊(2:ℝ)+2*Real.sqrt (m:ℝ)⌋₊ := by
  rw [P3_MAIN m hm,boundary_real_floor_eq]
  rfl

/-- P4's e=3 consequence uses V03's short binomial comparison. -/
theorem P4_e3 (m : ℕ) (hm : 4 ≤ m) : NSP3.P3_R m=C3 m ↔ m ≤ 9 := by
  rw [P3_MAIN m hm]
  exact macaulay_equality_iff m hm

end NSP3.V03
