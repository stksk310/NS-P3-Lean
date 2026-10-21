import NSP3.Main
namespace NSP3
example (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (R : Finset (AtomCoefficients (generatedSemigroup m a b c) × AtomCoefficients (generatedSemigroup m a b c)))
    (hR : IsAtomPresentation (generatedSemigroup m a b c) R)
    (hmin : ∀ T, T ⊂ R → ¬ IsAtomPresentation (generatedSemigroup m a b c) T) :
    R.card = intrinsicRho (generatedSemigroup m a b c) :=
  literature_common_cardinality_bridge m a b c h R hR hmin
end NSP3
