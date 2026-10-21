import NSP3.AtomFactorization
namespace NSP3
noncomputable example (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    Fact4 ≃+ AtomCoefficients (generatedSemigroup m a b c) := atomFactorEquiv m a b c h
example (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) (u : Fact4) :
    atomWeight _ (atomFactorEquiv m a b c h u) = factorWeight m a b c u :=
  atomFactorEquiv_weight m a b c h u
end NSP3
