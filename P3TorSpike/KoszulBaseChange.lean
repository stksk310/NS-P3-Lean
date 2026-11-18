import P3TorSpike.KoszulComplex
import Mathlib.LinearAlgebra.TensorProduct.Pi

noncomputable section
open scoped TensorProduct
namespace NSP3.TorSpike.Koszul
open CategoryTheory

section Generic
variable (S A : Type) [CommRing S] [CommRing A] [Algebra S A]

def baseCubeD (u : Fin 4 → A) (v : Fin 16 → A) : Fin 16 → A := ![
  u 0*v 1 + u 1*v 2 + u 2*v 4 + u 3*v 8,
  -u 1*v 3 - u 2*v 5 - u 3*v 9,
  u 0*v 3 - u 2*v 6 - u 3*v 10,
  u 2*v 7 + u 3*v 11,
  u 0*v 5 + u 1*v 6 - u 3*v 12,
  -u 1*v 7 + u 3*v 13,
  u 0*v 7 + u 3*v 14,
  -u 3*v 15,
  u 0*v 9 + u 1*v 10 + u 2*v 12,
  -u 1*v 11 - u 2*v 13,
  u 0*v 11 - u 2*v 14,
  u 2*v 15,
  u 0*v 13 + u 1*v 14,
  -u 1*v 15,
  u 0*v 15,
  0]

def baseCubeLinear (u : Fin 4 → A) : (Fin 16 → A) →ₗ[S] (Fin 16 → A) where
  toFun := baseCubeD A u
  map_add' v w := by funext i; fin_cases i <;> simp [baseCubeD] <;> ring
  map_smul' r v := by
    funext i
    fin_cases i <;> simp [baseCubeD, Algebra.smul_def] <;> ring

theorem baseCube_squared (u : Fin 4 → A) (v : Fin 16 → A) :
    baseCubeD A u (baseCubeD A u v) = 0 := by
  funext i; fin_cases i <;> simp [baseCubeD] <;> ring

def baseGraded (n : ℕ) : Submodule S (Fin 16 → A) where
  carrier := {v | ∀ i, degree i ≠ n → v i = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw i hi; simp [hv i hi, hw i hi]
  smul_mem' := by intro r v hv i hi; simp [hv i hi]

def baseGradedEquiv (n : ℕ) :
    baseGraded S A n ≃ₗ[S] ({i : Fin 16 // degree i = n} → A) where
  toFun v i := v.1 i.1
  invFun f := ⟨fun i => if h : degree i = n then f ⟨i,h⟩ else 0,
    fun i hi => dite_eq_right hi⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    by_cases hi : degree i = n
    · simp [hi]
    · simp [hi, v.2 i hi]
  right_inv f := by funext i; simp [i.2]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem baseCube_mem (u : Fin 4 → A) (n : ℕ) (v : baseGraded S A (n+1)) :
    baseCubeD A u v.1 ∈ baseGraded S A n := by
  intro i hi
  have hz (j : Fin 16) (hji : degree j = degree i + 1) : v.1 j = 0 :=
    v.2 j (fun he => hi (Nat.add_right_cancel (hji.symm.trans he)))
  fin_cases i
  · have h1 : v.1 1 = 0 := hz 1 (by decide)
    have h2 : v.1 2 = 0 := hz 2 (by decide)
    have h4 : v.1 4 = 0 := hz 4 (by decide)
    have h8 : v.1 8 = 0 := hz 8 (by decide)
    simp [baseCubeD, h1, h2, h4, h8]
  · have h3 : v.1 3 = 0 := hz 3 (by decide)
    have h5 : v.1 5 = 0 := hz 5 (by decide)
    have h9 : v.1 9 = 0 := hz 9 (by decide)
    simp [baseCubeD, h3, h5, h9]
  · have h3 : v.1 3 = 0 := hz 3 (by decide)
    have h6 : v.1 6 = 0 := hz 6 (by decide)
    have h10 : v.1 10 = 0 := hz 10 (by decide)
    simp [baseCubeD, h3, h6, h10]
  · have h7 : v.1 7 = 0 := hz 7 (by decide)
    have h11 : v.1 11 = 0 := hz 11 (by decide)
    simp [baseCubeD, h7, h11]
  · have h5 : v.1 5 = 0 := hz 5 (by decide)
    have h6 : v.1 6 = 0 := hz 6 (by decide)
    have h12 : v.1 12 = 0 := hz 12 (by decide)
    simp [baseCubeD, h5, h6, h12]
  · have h7 : v.1 7 = 0 := hz 7 (by decide)
    have h13 : v.1 13 = 0 := hz 13 (by decide)
    simp [baseCubeD, h7, h13]
  · have h7 : v.1 7 = 0 := hz 7 (by decide)
    have h14 : v.1 14 = 0 := hz 14 (by decide)
    simp [baseCubeD, h7, h14]
  · have h15 : v.1 15 = 0 := hz 15 (by decide)
    simp [baseCubeD, h15]
  · have h9 : v.1 9 = 0 := hz 9 (by decide)
    have h10 : v.1 10 = 0 := hz 10 (by decide)
    have h12 : v.1 12 = 0 := hz 12 (by decide)
    simp [baseCubeD, h9, h10, h12]
  · have h11 : v.1 11 = 0 := hz 11 (by decide)
    have h13 : v.1 13 = 0 := hz 13 (by decide)
    simp [baseCubeD, h11, h13]
  · have h11 : v.1 11 = 0 := hz 11 (by decide)
    have h14 : v.1 14 = 0 := hz 14 (by decide)
    simp [baseCubeD, h11, h14]
  · have h15 : v.1 15 = 0 := hz 15 (by decide)
    simp [baseCubeD, h15]
  · have h13 : v.1 13 = 0 := hz 13 (by decide)
    have h14 : v.1 14 = 0 := hz 14 (by decide)
    simp [baseCubeD, h13, h14]
  · have h15 : v.1 15 = 0 := hz 15 (by decide)
    simp [baseCubeD, h15]
  · have h15 : v.1 15 = 0 := hz 15 (by decide)
    simp [baseCubeD, h15]
  · simp [baseCubeD]
def baseDifferential (u : Fin 4 → A) (n : ℕ) :
    baseGraded S A (n+1) →ₗ[S] baseGraded S A n :=
  (baseCubeLinear S A u).restrict (fun v hv => baseCube_mem S A u n ⟨v,hv⟩)

theorem baseDifferential_squared (u : Fin 4 → A) (n : ℕ) :
    (baseDifferential S A u n).comp (baseDifferential S A u (n+1)) = 0 := by
  ext v
  exact congrFun (baseCube_squared A u v.1) _

def baseComplex (u : Fin 4 → A) : ChainComplex (ModuleCat S) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of S (baseGraded S A n))
    (fun n => ModuleCat.ofHom (baseDifferential S A u n))
    (fun n => ModuleCat.hom_ext (baseDifferential_squared S A u n))

end Generic

section Tensor
variable (k A : Type) [Field k] [CommRing A] [Algebra (PolynomialRing k) A]

def tensorGradedEquiv (n : ℕ) :
    A ⊗[PolynomialRing k] graded k n ≃ₗ[PolynomialRing k]
      baseGraded (PolynomialRing k) A n := by
  classical
  exact (TensorProduct.congr (LinearEquiv.refl (PolynomialRing k) A) (gradedEquiv k n)).trans
    ((TensorProduct.piScalarRight (PolynomialRing k) (PolynomialRing k) A
      {i : Fin 16 // degree i = n}).trans (baseGradedEquiv (PolynomialRing k) A n).symm)

@[simp] theorem tensorGradedEquiv_tmul (n : ℕ) (a : A) (v : graded k n) (i : Fin 16) :
    (tensorGradedEquiv k A n (a ⊗ₜ[PolynomialRing k] v)).val i = v.val i • a := by
  classical
  by_cases hi : degree i = n
  · simp [tensorGradedEquiv, baseGradedEquiv, gradedEquiv, hi]
  · simp [tensorGradedEquiv, baseGradedEquiv, hi, v.2 i hi]

def baseGenerators : Fin 4 → A := fun i => algebraMap (PolynomialRing k) A (MvPolynomial.X i)

theorem tensorDifferential_compat (n : ℕ) :
    (baseDifferential (PolynomialRing k) A (baseGenerators k A) n).comp
        (tensorGradedEquiv k A (n+1)).toLinearMap =
      (tensorGradedEquiv k A n).toLinearMap.comp
        (TensorProduct.map (LinearMap.id : A →ₗ[PolynomialRing k] A)
          (gradedDifferential k n)) := by
  ext a v i
  change baseCubeD A (baseGenerators k A)
      (tensorGradedEquiv k A (n+1) (a ⊗ₜ[PolynomialRing k] v)).val i =
    (tensorGradedEquiv k A n
      (a ⊗ₜ[PolynomialRing k] gradedDifferential k n v)).val i
  rw [tensorGradedEquiv_tmul]
  change baseCubeD A (baseGenerators k A)
      (tensorGradedEquiv k A (n+1) (a ⊗ₜ[PolynomialRing k] v)).val i =
    differential v.val i • a
  fin_cases i <;>
    simp [baseCubeD, differential, baseGenerators, tensorGradedEquiv_tmul,
      Algebra.smul_def, map_add, map_sub, map_neg, map_mul] <;> ring

end Tensor
end NSP3.TorSpike.Koszul
