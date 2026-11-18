import P3TorSpike.RegularReductionCone
import P3TorSpike.ReductionComplex
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NSP3.TorSpike.RegularReduction
open CategoryTheory
variable (k R : Type) [Field k] [CommRing R] [Algebra k R]

abbrev QuotientRing (t : R) := R ⧸ Ideal.span ({t} : Set R)

def quotientAlg (t : R) : R →ₐ[k] QuotientRing R t := Ideal.Quotient.mkₐ k _

def multiply (t : R) : R →ₗ[k] R := LinearMap.mul k R t

def quotientPi (t : R) (ι : Type) : (ι → R) →ₗ[k] (ι → QuotientRing R t) :=
  LinearMap.pi (fun i => (quotientAlg k R t).toLinearMap.comp (LinearMap.proj i))

def multiplyPi (t : R) (ι : Type) : (ι → R) →ₗ[k] (ι → R) :=
  LinearMap.pi (fun i => (multiply k R t).comp (LinearMap.proj i))

@[simp] theorem multiply_apply (t x : R) : multiply k R t x = t*x := rfl
@[simp] theorem quotientPi_apply (t : R) (ι : Type) (v : ι → R) (i : ι) :
    quotientPi k R t ι v i = quotientAlg k R t (v i) := rfl
@[simp] theorem multiplyPi_apply (t : R) (ι : Type) (v : ι → R) (i : ι) :
    multiplyPi k R t ι v i = t*v i := rfl

theorem quotient_surjective (t : R) : Function.Surjective (quotientAlg k R t) :=
  Ideal.Quotient.mkₐ_surjective k _

theorem quotientPi_surjective (t : R) (ι : Type) : Function.Surjective (quotientPi k R t ι) := by
  intro v
  choose w hw using fun i => quotient_surjective k R t (v i)
  exact ⟨w,funext hw⟩

theorem range_multiply_eq_ker_quotient (t : R) :
    LinearMap.range (multiply k R t) = LinearMap.ker (quotientAlg k R t).toLinearMap := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    change Ideal.Quotient.mk _ (t*y) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_span_singleton.mpr ⟨y,rfl⟩
  · intro hx
    have hi : x ∈ Ideal.span ({t} : Set R) := Ideal.Quotient.eq_zero_iff_mem.mp hx
    obtain ⟨y,hy⟩ := Ideal.mem_span_singleton.mp hi
    exact ⟨y,hy.symm⟩

theorem range_multiplyPi_eq_ker_quotientPi (t : R) (ι : Type) :
    LinearMap.range (multiplyPi k R t ι) = LinearMap.ker (quotientPi k R t ι) := by
  ext v
  constructor
  · rintro ⟨w,rfl⟩
    ext i
    have hmem : multiply k R t (w i) ∈ LinearMap.ker (quotientAlg k R t).toLinearMap := by
      rw [← range_multiply_eq_ker_quotient]
      exact ⟨w i,rfl⟩
    exact hmem
  · intro hv
    have hvi (i : ι) : v i ∈ LinearMap.range (multiply k R t) := by
      rw [range_multiply_eq_ker_quotient]
      exact congrFun hv i
    choose w hw using hvi
    exact ⟨w,funext hw⟩

theorem multiplyPi_injective (t : R) (ht : Function.Injective (multiply k R t)) (ι : Type) :
    Function.Injective (multiplyPi k R t ι) := by
  intro v w h
  funext i
  exact ht (congrFun h i)

def multiplyH1 (t : R) (u : Fin 3 → R) : threeH1Complex k R u ⟶ threeH1Complex k R u where
  τ₁ := ModuleCat.ofHom (multiplyPi k R t (Fin 3))
  τ₂ := ModuleCat.ofHom (multiplyPi k R t (Fin 3))
  τ₃ := ModuleCat.ofHom (multiply k R t)
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change threeD2 k R u (multiplyPi k R t (Fin 3) v) =
      multiplyPi k R t (Fin 3) (threeD2 k R u v)
    funext i
    fin_cases i <;> simp [threeD2_apply, multiplyPi, multiply, threeD2] <;> ring
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change threeD1 k R u (multiplyPi k R t (Fin 3) v) = multiply k R t (threeD1 k R u v)
    simp [threeD1_apply, multiplyPi, multiply, threeD1]
    ring

def quotientH1 (t : R) (u : Fin 3 → R) :
    threeH1Complex k R u ⟶ threeH1Complex k (QuotientRing R t) (fun i => quotientAlg k R t (u i)) where
  τ₁ := ModuleCat.ofHom (quotientPi k R t (Fin 3))
  τ₂ := ModuleCat.ofHom (quotientPi k R t (Fin 3))
  τ₃ := ModuleCat.ofHom (quotientAlg k R t).toLinearMap
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change threeD2 k (QuotientRing R t) (fun i => quotientAlg k R t (u i))
      (quotientPi k R t (Fin 3) v) = quotientPi k R t (Fin 3) (threeD2 k R u v)
    funext i
    fin_cases i <;> simp [threeD2_apply, quotientPi, threeD2]
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change threeD1 k (QuotientRing R t) (fun i => quotientAlg k R t (u i))
      (quotientPi k R t (Fin 3) v) = quotientAlg k R t (threeD1 k R u v)
    simp [threeD1_apply, quotientPi, threeD1]
/-- Actual degree-one cone homology is the first Koszul homology over the quotient ring. -/
def regularH1Equiv (t : R) (u : Fin 3 → R) (ht : Function.Injective (multiply k R t)) :
    (coneShortComplex (threeH1Complex k R u) (multiplyH1 k R t u)
      (0 : R →ₗ[k] (Fin 0 → R)) (by rfl)).homology ≃ₗ[k]
    (threeH1Complex k (QuotientRing R t) (fun i => quotientAlg k R t (u i))).homology := by
  apply coneQuotientHomologyEquiv (quotientH1 k R t u)
    (0 : R →ₗ[k] (Fin 0 → R)) (by rfl) (0 : (Fin 0 → R) →ₗ[k] (Fin 0 → R))
  · rfl
  · exact ht
  · exact fun _ _ _ => Subsingleton.elim _ _
  · exact range_multiplyPi_eq_ker_quotientPi k R t (Fin 3)
  · exact range_multiply_eq_ker_quotient k R t
  · exact quotientPi_surjective k R t (Fin 3)
  · exact quotientPi_surjective k R t (Fin 3)

end NSP3.TorSpike.RegularReduction
