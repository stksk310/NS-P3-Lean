import P3TorSpike.TorObjects
import P3TorSpike.Augmentation

noncomputable section
open scoped TensorProduct
namespace NSP3.TorSpike

/-- Tensoring a quotient algebra with a compatible residue algebra removes the quotient. -/
def quotientTensorEquiv (P R K : Type) [CommRing P] [CommRing R] [CommRing K]
    [Algebra P R] [Algebra P K] (f : R →ₐ[P] K)
    (hs : Function.Surjective (algebraMap P R)) : R ⊗[P] K ≃ₗ[P] K := by
  let forward : R ⊗[P] K →ₗ[P] K := TensorProduct.lift ((LinearMap.mul P K).comp f.toLinearMap)
  refine {forward with invFun := fun c => (1:R) ⊗ₜ[P] c, left_inv := ?_, right_inv := ?_}
  · intro t
    change (1:R) ⊗ₜ[P] (forward t)=t
    induction t using TensorProduct.induction_on with
    | zero => simp [forward]
    | tmul r c =>
      obtain ⟨p,rfl⟩ := hs r
      simp only [forward,TensorProduct.lift.tmul,LinearMap.comp_apply,
        AlgHom.toLinearMap_apply,LinearMap.mul_apply',AlgHom.commutes]
      rw [← Algebra.smul_def, ← TensorProduct.smul_tmul]
      simp [Algebra.smul_def]
    | add t u ht hu => rw [map_add,TensorProduct.tmul_add,ht,hu]
  · intro c
    change forward ((1:R) ⊗ₜ[P] c)=c
    simp [forward,LinearMap.mul_apply']

def residueAlgebra (k : Type) [Field k] : Algebra (PolynomialRing k) k :=
  (MvPolynomial.constantCoeff : PolynomialRing k →+* k).toAlgebra

def semigroupAlgebra (k : Type) [Field k] (m a b c : ℕ) :
    Algebra (PolynomialRing k) (SemigroupRing k m a b c) :=
  (polynomialMap k m a b c).toRingHom.toAlgebra

def augmentationOverP (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    letI := residueAlgebra k
    letI := semigroupAlgebra k m a b c
    SemigroupRing k m a b c →ₐ[PolynomialRing k] k := by
  letI := residueAlgebra k
  letI := semigroupAlgebra k m a b c
  refine { (augmentation k m a b c).toRingHom with commutes' := ?_ }
  intro p
  have he := congrArg (fun F : PolynomialRing k →ₐ[k] k => F p)
    (augmentation_polynomialMap k m a b c h)
  change augmentation k m a b c (polynomialMap k m a b c p)=MvPolynomial.constantCoeff p
  simpa using he

end NSP3.TorSpike
