import NSP3.Main

namespace NSP3

example (S : AddSubmonoid ℕ) (m : ℕ)
    (hcof : ((S : Set ℕ)ᶜ).Finite)
    (hedim : semigroupEmbeddingDimension (S : Set ℕ) = 4)
    (hm : IsSemigroupMultiplicity (S : Set ℕ) m) :
    ∃ a b c : ℕ, MinimalFourGeneratorClass m a b c ∧
      generatedAddSubmonoid m a b c = S :=
  numerical_semigroup_class_coverage S m hcof hedim hm

end NSP3
