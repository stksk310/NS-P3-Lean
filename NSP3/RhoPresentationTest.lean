import NSP3.RhoPresentation
namespace NSP3
example (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    intrinsicRho (generatedSemigroup m a b c) = minimumFourInputRelations m a b c :=
  literature_rho_identification m a b c h
example (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    intrinsicRho (generatedSemigroup m a b c) ≤ ⌊(2 : ℝ)+2*Real.sqrt (m : ℝ)⌋₊ :=
  intrinsic_rho_real_sharp m a b c h
end NSP3
