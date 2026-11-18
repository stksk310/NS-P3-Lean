import P3TorSpike.BinomialInterface
import P3TorSpike.Augmentation

noncomputable section
namespace NSP3.TorSpike

/-- The chosen monomial section is a genuine right inverse on the actual semigroup algebra. -/
@[simp] theorem polynomialMap_normalSection (k : Type) [Field k] (m a b c : ℕ)
    (r : SemigroupRing k m a b c) :
    polynomialMap k m a b c (normalSection k m a b c r) = r := by
  induction r using AddMonoidAlgebra.induction_on with
  | of s =>
    change polynomialMap k m a b c (normalSection k m a b c (monomial k s)) = monomial k s
    rw [normalSection_monomial, polynomialMap_factMonomial, factorElement_chosenFactor]
  | add r s hr hs => simp only [map_add, hr, hs]
  | smul q r hr => simp only [map_smul, hr]

/-- The genuine polynomial kernel consists of polynomials with zero augmentation. -/
theorem relationKernel_le_augmentation (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    relationKernel k m a b c ≤ RingHom.ker (polynomialAugmentation k).toRingHom := by
  intro p hp
  change polynomialAugmentation k p = 0
  have hh := congrArg (fun f : PolynomialRing k →ₐ[k] k => f p)
    (augmentation_polynomialMap k m a b c h)
  calc
    polynomialAugmentation k p = augmentation k m a b c (polynomialMap k m a b c p) := hh.symm
    _ = 0 := by rw [show polynomialMap k m a b c p = 0 from hp, map_zero]

theorem relationKernel_constantCoeff_zero (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (x : relationKernel k m a b c) :
    MvPolynomial.constantCoeff (x : PolynomialRing k) = 0 := by
  rw [← polynomialAugmentation_eq_constantCoeff]
  exact relationKernel_le_augmentation k m a b c h x.property

end NSP3.TorSpike
