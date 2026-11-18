import P3TorSpike.BinomialConormal

noncomputable section
namespace NSP3.TorSpike

@[simp] theorem polynomialAugmentation_eq_constantCoeff (k : Type) [Field k]
    (p : PolynomialRing k) : polynomialAugmentation k p = MvPolynomial.constantCoeff p := by
  simp [polynomialAugmentation]

set_option backward.isDefEq.respectTransparency false in
theorem relationKernel_augmentationSubmodule_map (k : Type) [Field k] (m a b c : ℕ) :
    (augmentationSubmodule (M := relationKernel k m a b c) (polynomialAugmentation k)).map
        (relationKernel k m a b c).subtype =
      RingHom.ker (polynomialAugmentation k).toRingHom * relationKernel k m a b c := by
  rw [augmentationSubmodule, Submodule.map_smul'' _ ⊤ (Submodule.subtype _),
    smul_eq_mul, Submodule.map_subtype_top]

theorem relationKernel_mem_augmentationSubmodule (k : Type) [Field k] (m a b c : ℕ)
    (x : relationKernel k m a b c) :
    x ∈ augmentationSubmodule (M := relationKernel k m a b c) (polynomialAugmentation k) ↔
      (x : PolynomialRing k) ∈ RingHom.ker (polynomialAugmentation k).toRingHom *
        relationKernel k m a b c := by
  rw [← relationKernel_augmentationSubmodule_map]
  simp

theorem relationConormal_mk_eq_zero (k : Type) [Field k] (m a b c : ℕ)
    (x : relationKernel k m a b c) :
    (Submodule.Quotient.mk x : relationConormal k m a b c) = 0 ↔
      (x : PolynomialRing k) ∈ RingHom.ker (polynomialAugmentation k).toRingHom *
        relationKernel k m a b c := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact relationKernel_mem_augmentationSubmodule k m a b c x

end NSP3.TorSpike
