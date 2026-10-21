import NSP3.Main
namespace NSP3
example (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    intrinsicRho (generatedSemigroup m a b c) = minimumFourInputRelations m a b c :=
  literature_rho_identification m a b c h
end NSP3
