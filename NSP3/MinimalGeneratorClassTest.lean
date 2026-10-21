import NSP3.MinimalGeneratorClass

namespace NSP3
-- Catches defining atoms by generator membership or assuming multiplicity/edim in the class.
example (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    IsSemigroupMultiplicity (generatedSemigroup m a b c) m ∧
    (∀ n, SemigroupAtom (generatedSemigroup m a b c) n ↔ n ∈ ([m,a,b,c] : List ℕ)) ∧
    semigroupEmbeddingDimension (generatedSemigroup m a b c) = 4 ∧
    (generatedSemigroup m a b c)ᶜ.Finite :=
  minimal_generator_class_bridge m a b c h

example (m a c : ℕ) : ¬ MinimalFourGeneratorClass m a a c := by
  intro h
  have := h.distinct
  simp at this

example (a b c : ℕ) : ¬ MinimalFourGeneratorClass 0 a b c := by
  intro h
  have := h.positive
  omega

example : ¬ MinimalFourGeneratorClass 4 5 6 8 := by
  intro h
  have ha := h.atoms 8 (by simp)
  have hg := (generatedSemigroup_generators 4 5 6 8).1
  have := ha.2.2 4 hg 4 hg (by decide)
  omega

/-- A genuine nonempty minimal-four class, with atoms proved by additive indecomposability. -/
example : MinimalFourGeneratorClass 4 5 6 7 := by
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
end NSP3
