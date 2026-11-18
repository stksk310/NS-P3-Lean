import P3TorSpike.TensorResidue

noncomputable section
namespace NSP3.TorSpike

def torZeroEquivResidue (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    torModule k m a b c 0 ≃ₗ[PolynomialRing k] residueModule k := by
  letI := residueAlgebra k
  letI := semigroupAlgebra k m a b c
  exact (torZeroIsoTensor k m a b c).toLinearEquiv.trans
    (quotientTensorEquiv (PolynomialRing k) (SemigroupRing k m a b c) k
      (augmentationOverP k m a b c h) (polynomialMap_surjective k m a b c))

def restrictEquivToField (k : Type) [Field k] (M : ModuleCat.{0} (PolynomialRing k))
    (f : M ≃ₗ[PolynomialRing k] residueModule k) :
    letI : Module k M := Module.compHom M (algebraMap k (PolynomialRing k))
    M ≃ₗ[k] k := by
  letI : Module k M := Module.compHom M (algebraMap k (PolynomialRing k))
  letI : Module (PolynomialRing k) k := Module.compHom k MvPolynomial.constantCoeff
  let e : M ≃ₗ[PolynomialRing k] k := f
  refine {e.toEquiv with map_add' := e.map_add, map_smul' := ?_}
  intro r x
  have he := e.map_smul (MvPolynomial.C r : PolynomialRing k) x
  change e ((MvPolynomial.C r : PolynomialRing k) • x)=r*e x
  rw [he]
  change MvPolynomial.constantCoeff (MvPolynomial.C r)*e x=r*e x
  rw [MvPolynomial.constantCoeff_C]

def torZeroEquivField (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :=
  restrictEquivToField k (torModule k m a b c 0) (torZeroEquivResidue k m a b c h)

theorem restrictedRank_eq_one (k : Type) [Field k] (M : ModuleCat.{0} (PolynomialRing k))
    (f : M ≃ₗ[PolynomialRing k] residueModule k) :
    letI : Module k M := Module.compHom M (algebraMap k (PolynomialRing k))
    Module.rank k M=1 := by
  letI : Module k M := Module.compHom M (algebraMap k (PolynomialRing k))
  exact (restrictEquivToField k M f).rank_eq.trans (Module.rank_self k)

/-- Actual Tor has cardinal dimension one in degree zero. -/
theorem torDimension_zero (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) : torDimension k m a b c 0=1 :=
  restrictedRank_eq_one k (torModule k m a b c 0) (torZeroEquivResidue k m a b c h)

theorem restrictedFinite (k : Type) [Field k] (M : ModuleCat.{0} (PolynomialRing k))
    (f : M ≃ₗ[PolynomialRing k] residueModule k) :
    letI : Module k M := Module.compHom M (algebraMap k (PolynomialRing k))
    Module.Finite k M := by
  letI : Module k M := Module.compHom M (algebraMap k (PolynomialRing k))
  exact Module.Finite.of_surjective (restrictEquivToField k M f).symm.toLinearMap
    (restrictEquivToField k M f).symm.surjective

theorem restrictedFinrank_eq_one (k : Type) [Field k] (M : ModuleCat.{0} (PolynomialRing k))
    (f : M ≃ₗ[PolynomialRing k] residueModule k) :
    letI : Module k M := Module.compHom M (algebraMap k (PolynomialRing k))
    Module.finrank k M=1 := by
  letI : Module k M := Module.compHom M (algebraMap k (PolynomialRing k))
  exact (restrictEquivToField k M f).finrank_eq.trans (by simp)

theorem torZero_finite (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    letI := torVectorModule k m a b c 0
    Module.Finite k (torModule k m a b c 0) :=
  restrictedFinite k (torModule k m a b c 0) (torZeroEquivResidue k m a b c h)

theorem torFinrank_zero (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    letI := torVectorModule k m a b c 0
    Module.finrank k (torModule k m a b c 0)=1 :=
  restrictedFinrank_eq_one k (torModule k m a b c 0) (torZeroEquivResidue k m a b c h)

end NSP3.TorSpike
