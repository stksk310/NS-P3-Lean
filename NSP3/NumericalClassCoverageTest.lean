import NSP3.NumericalClassCoverage

namespace NSP3

example (S : AddSubmonoid ℕ) (m : ℕ)
    (hcof : ((S : Set ℕ)ᶜ).Finite)
    (hedim : semigroupEmbeddingDimension (S : Set ℕ) = 4)
    (hm : IsSemigroupMultiplicity (S : Set ℕ) m) :
    ∃ a b c : ℕ, MinimalFourGeneratorClass m a b c ∧
      generatedAddSubmonoid m a b c = S :=
  numerical_semigroup_class_coverage S m hcof hedim hm

example (S : AddSubmonoid ℕ) (m : ℕ)
    (hcof : ((S : Set ℕ)ᶜ).Finite)
    (hedim : semigroupEmbeddingDimension (S : Set ℕ) = 4)
    (hm : IsSemigroupMultiplicity (S : Set ℕ) m) :
    intrinsicRho (S : Set ℕ) ≤ ⌊(2 : ℝ)+2*Real.sqrt (m : ℝ)⌋₊ :=
  numerical_semigroup_all_edim4_rho_upper S m hcof hedim hm

example (S : AddSubmonoid ℕ) (m : ℕ)
    (hcof : ((S : Set ℕ)ᶜ).Finite)
    (hedim : semigroupEmbeddingDimension (S : Set ℕ) = 4)
    (hm : IsSemigroupMultiplicity (S : Set ℕ) m)
    (R : Finset (AtomCoefficients (S : Set ℕ) × AtomCoefficients (S : Set ℕ)))
    (hR : IsAtomPresentation (S : Set ℕ) R)
    (hmin : ∀ T, T ⊂ R → ¬ IsAtomPresentation (S : Set ℕ) T) :
    R.card = intrinsicRho (S : Set ℕ) ∧ R.card ≤ ⌊(2 : ℝ)+2*Real.sqrt (m : ℝ)⌋₊ :=
  ⟨numerical_semigroup_minimal_presentation_card S m hcof hedim hm R hR hmin,
    numerical_semigroup_minimal_presentation_upper S m hcof hedim hm R hR hmin⟩

private theorem fixture : MinimalFourGeneratorClass 4 5 6 7 := by
  have lower : ∀ n ∈ generatedSemigroup 4 5 6 7, 0 < n → 4 ≤ n := by
    rintro n ⟨k,x,y,z,rfl⟩ hn
    by_cases hk : k=0
    · by_cases hx : x=0
      · by_cases hy : y=0 <;> omega
      · omega
    · omega
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro g hg
  have hb : 4 ≤ g ∧ g ≤ 7 := by simp at hg; omega
  have hin : g ∈ generatedSemigroup 4 5 6 7 := by
    have hh := generatedSemigroup_generators 4 5 6 7
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hh.1
    · exact hh.2.1
    · exact hh.2.2.1
    · exact hh.2.2.2
  refine ⟨hin, by omega, ?_⟩
  intro x hx y hy he
  by_cases hx0 : x=0
  · exact Or.inl hx0
  by_cases hy0 : y=0
  · exact Or.inr hy0
  have := lower x hx (by omega)
  have := lower y hy (by omega)
  omega

example : ∃ a b c, MinimalFourGeneratorClass 4 a b c ∧
    generatedAddSubmonoid 4 a b c = generatedAddSubmonoid 4 5 6 7 :=
  numerical_semigroup_class_coverage (generatedAddSubmonoid 4 5 6 7) 4
    (minimal_generator_class_bridge 4 5 6 7 fixture).2.2.2
    (minimalFour_embeddingDimension 4 5 6 7 fixture)
    (minimalFour_multiplicity 4 5 6 7 fixture)

-- The redundant input 8=4+4 is not an atom of the actual semigroup.
example : ¬ SemigroupAtom (generatedSemigroup 4 5 6 7) 8 := by
  intro h
  have h4 := (generatedSemigroup_generators 4 5 6 7).1
  have := h.2.2 4 h4 4 h4 (by decide)
  omega

example : ¬ MinimalFourGeneratorClass 4 5 6 8 := by
  intro h
  have h8 := h.atoms 8 (by simp)
  have h4 := (generatedSemigroup_generators 4 5 6 8).1
  have := h8.2.2 4 h4 4 h4 (by decide)
  omega

end NSP3
