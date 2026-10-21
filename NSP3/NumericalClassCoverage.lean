import NSP3.CoverageAtoms
import NSP3.CoverageFourAtoms
import NSP3.CoverageArithmetic
import NSP3.CommonCardBridge

namespace NSP3

theorem numerical_semigroup_class_coverage
    (S : AddSubmonoid ℕ) (m : ℕ)
    (hcof : ((S : Set ℕ)ᶜ).Finite)
    (hedim : semigroupEmbeddingDimension (S : Set ℕ) = 4)
    (hm : IsSemigroupMultiplicity (S : Set ℕ) m) :
    ∃ a b c : ℕ, MinimalFourGeneratorClass m a b c ∧
      generatedAddSubmonoid m a b c = S := by
  obtain ⟨a,b,c,hdistinct,hatoms⟩ := Coverage.four_atoms_of_finite_edim_four
    (S : Set ℕ) m (Coverage.atoms_finite S hcof hm) hedim (Coverage.multiplicity_atom S hm)
  have ha : SemigroupAtom (S : Set ℕ) a := (hatoms a).mpr (by simp)
  have hb : SemigroupAtom (S : Set ℕ) b := (hatoms b).mpr (by simp)
  have hc : SemigroupAtom (S : Set ℕ) c := (hatoms c).mpr (by simp)
  have heq : generatedAddSubmonoid m a b c = S := by
    apply le_antisymm (Coverage.generated_le S m a b c hm.1 ha.1 hb.1 hc.1)
    apply Coverage.atoms_generate S (generatedAddSubmonoid m a b c)
    intro n hn
    have hg := generatedSemigroup_generators m a b c
    have hmem := (hatoms n).mp hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · exact hg.1
    · exact hg.2.1
    · exact hg.2.2.1
    · exact hg.2.2.2
  have hset : generatedSemigroup m a b c = (S : Set ℕ) :=
    congrArg (fun T : AddSubmonoid ℕ => (T : Set ℕ)) heq
  obtain ⟨C,hC,htail⟩ := Coverage.cofinite_tail S hcof
  refine ⟨a,b,c,?_,heq⟩
  refine ⟨hdistinct,hm.2.1,hm.2.2 a ha.1 ha.2.1,
    hm.2.2 b hb.1 hb.2.1,hm.2.2 c hc.1 hc.2.1,?_,?_⟩
  · apply Coverage.gcd_eq_one_of_tail m a b c C
    intro n hn
    rw [hset]
    exact htail n hn
  · intro n hn
    rw [hset]
    exact (hatoms n).mpr hn

theorem numerical_semigroup_all_edim4_rho_upper
    (S : AddSubmonoid ℕ) (m : ℕ)
    (hcof : ((S : Set ℕ)ᶜ).Finite)
    (hedim : semigroupEmbeddingDimension (S : Set ℕ) = 4)
    (hm : IsSemigroupMultiplicity (S : Set ℕ) m) :
    intrinsicRho (S : Set ℕ) ≤ ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ := by
  obtain ⟨a,b,c,h,heq⟩ := numerical_semigroup_class_coverage S m hcof hedim hm
  have hset : generatedSemigroup m a b c = (S : Set ℕ) :=
    congrArg (fun T : AddSubmonoid ℕ => (T : Set ℕ)) heq
  simpa only [hset] using intrinsic_rho_real_sharp m a b c h

theorem numerical_semigroup_minimal_presentation_card
    (S : AddSubmonoid ℕ) (m : ℕ)
    (hcof : ((S : Set ℕ)ᶜ).Finite)
    (hedim : semigroupEmbeddingDimension (S : Set ℕ) = 4)
    (hm : IsSemigroupMultiplicity (S : Set ℕ) m)
    (R : Finset (AtomCoefficients (S : Set ℕ) × AtomCoefficients (S : Set ℕ)))
    (hR : IsAtomPresentation (S : Set ℕ) R)
    (hmin : ∀ T, T ⊂ R → ¬ IsAtomPresentation (S : Set ℕ) T) :
    R.card = intrinsicRho (S : Set ℕ) := by
  obtain ⟨a,b,c,h,heq⟩ := numerical_semigroup_class_coverage S m hcof hedim hm
  have hset : generatedSemigroup m a b c = (S : Set ℕ) :=
    congrArg (fun T : AddSubmonoid ℕ => (T : Set ℕ)) heq
  have ht := literature_common_cardinality_bridge m a b c h
  rw [hset] at ht
  exact ht R hR hmin

theorem numerical_semigroup_minimal_presentation_upper
    (S : AddSubmonoid ℕ) (m : ℕ)
    (hcof : ((S : Set ℕ)ᶜ).Finite)
    (hedim : semigroupEmbeddingDimension (S : Set ℕ) = 4)
    (hm : IsSemigroupMultiplicity (S : Set ℕ) m)
    (R : Finset (AtomCoefficients (S : Set ℕ) × AtomCoefficients (S : Set ℕ)))
    (hR : IsAtomPresentation (S : Set ℕ) R)
    (hmin : ∀ T, T ⊂ R → ¬ IsAtomPresentation (S : Set ℕ) T) :
    R.card ≤ ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ := by
  rw [numerical_semigroup_minimal_presentation_card S m hcof hedim hm R hR hmin]
  exact numerical_semigroup_all_edim4_rho_upper S m hcof hedim hm

end NSP3
