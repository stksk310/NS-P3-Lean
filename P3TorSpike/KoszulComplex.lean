import P3TorSpike.KoszulCube
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

noncomputable section
namespace NSP3.TorSpike.Koszul
open CategoryTheory
variable {k : Type} [Field k]

/-- Exterior degree of the binary-order basis. -/
def degree : Fin 16 → ℕ := ![0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4]

/-- The actual homogeneous exterior-degree summand in the free polynomial cube. -/
def graded (k : Type) [Field k] (n : ℕ) : Submodule (PolynomialRing k) (Cube k) where
  carrier := {v | ∀ i, degree i ≠ n → v i = 0}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb i hi; simp [ha i hi, hb i hi]
  smul_mem' := by intro r a ha i hi; simp [ha i hi]

/-- Canonical coordinates exhibit each homogeneous summand as a finite free module. -/
def gradedEquiv (k : Type) [Field k] (n : ℕ) :
    graded k n ≃ₗ[PolynomialRing k] ({i : Fin 16 // degree i = n} → PolynomialRing k) where
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
  map_add' a b := rfl
  map_smul' a b := rfl

instance graded_free (k : Type) [Field k] (n : ℕ) :
    Module.Free (PolynomialRing k) (graded k n) :=
  Module.Free.of_equiv (gradedEquiv k n).symm

instance graded_finite (k : Type) [Field k] (n : ℕ) :
    Module.Finite (PolynomialRing k) (graded k n) :=
  Module.Finite.equiv (gradedEquiv k n).symm

theorem differential_mem (n : ℕ) (v : graded k (n+1)) :
    differential v.1 ∈ graded k n := by
  intro i hi
  have hz (j : Fin 16) (hji : degree j = degree i + 1) : v.1 j = 0 :=
    v.2 j (fun he => hi (Nat.add_right_cancel (hji.symm.trans he)))
  fin_cases i
  · have h1 : v.1 1 = 0 := hz 1 (by decide)
    have h2 : v.1 2 = 0 := hz 2 (by decide)
    have h4 : v.1 4 = 0 := hz 4 (by decide)
    have h8 : v.1 8 = 0 := hz 8 (by decide)
    simp [differential, h1, h2, h4, h8]
  · have h3 : v.1 3 = 0 := hz 3 (by decide)
    have h5 : v.1 5 = 0 := hz 5 (by decide)
    have h9 : v.1 9 = 0 := hz 9 (by decide)
    simp [differential, h3, h5, h9]
  · have h3 : v.1 3 = 0 := hz 3 (by decide)
    have h6 : v.1 6 = 0 := hz 6 (by decide)
    have h10 : v.1 10 = 0 := hz 10 (by decide)
    simp [differential, h3, h6, h10]
  · have h7 : v.1 7 = 0 := hz 7 (by decide)
    have h11 : v.1 11 = 0 := hz 11 (by decide)
    simp [differential, h7, h11]
  · have h5 : v.1 5 = 0 := hz 5 (by decide)
    have h6 : v.1 6 = 0 := hz 6 (by decide)
    have h12 : v.1 12 = 0 := hz 12 (by decide)
    simp [differential, h5, h6, h12]
  · have h7 : v.1 7 = 0 := hz 7 (by decide)
    have h13 : v.1 13 = 0 := hz 13 (by decide)
    simp [differential, h7, h13]
  · have h7 : v.1 7 = 0 := hz 7 (by decide)
    have h14 : v.1 14 = 0 := hz 14 (by decide)
    simp [differential, h7, h14]
  · have h15 : v.1 15 = 0 := hz 15 (by decide)
    simp [differential, h15]
  · have h9 : v.1 9 = 0 := hz 9 (by decide)
    have h10 : v.1 10 = 0 := hz 10 (by decide)
    have h12 : v.1 12 = 0 := hz 12 (by decide)
    simp [differential, h9, h10, h12]
  · have h11 : v.1 11 = 0 := hz 11 (by decide)
    have h13 : v.1 13 = 0 := hz 13 (by decide)
    simp [differential, h11, h13]
  · have h11 : v.1 11 = 0 := hz 11 (by decide)
    have h14 : v.1 14 = 0 := hz 14 (by decide)
    simp [differential, h11, h14]
  · have h15 : v.1 15 = 0 := hz 15 (by decide)
    simp [differential, h15]
  · have h13 : v.1 13 = 0 := hz 13 (by decide)
    have h14 : v.1 14 = 0 := hz 14 (by decide)
    simp [differential, h13, h14]
  · have h15 : v.1 15 = 0 := hz 15 (by decide)
    simp [differential, h15]
  · have h15 : v.1 15 = 0 := hz 15 (by decide)
    simp [differential, h15]
  · simp [differential]
def gradedDifferential (k : Type) [Field k] (n : ℕ) :
    graded k (n+1) →ₗ[PolynomialRing k] graded k n :=
  (differentialLinear k).restrict (fun x hx => differential_mem n ⟨x, hx⟩)

theorem gradedDifferential_squared (k : Type) [Field k] (n : ℕ) :
    (gradedDifferential k n).comp (gradedDifferential k (n+1)) = 0 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  exact differential_squared v.1

/-- The finite free, four-variable polynomial Koszul chain complex. -/
def complex (k : Type) [Field k] : ChainComplex (ModuleCat (PolynomialRing k)) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of _ (graded k n))
    (fun n => ModuleCat.ofHom (gradedDifferential k n))
    (fun n => ModuleCat.hom_ext (gradedDifferential_squared k n))

instance complex_projective (k : Type) [Field k] (n : ℕ) :
    CategoryTheory.Projective ((complex k).X n) := by
  change CategoryTheory.Projective (ModuleCat.of _ (graded k n))
  infer_instance

theorem contraction_mem (n : ℕ) (v : graded k n) :
    contraction v.1 ∈ graded k (n+1) := by
  intro i hi
  have hs (j : Fin 16) (hji : degree i = degree j + 1) : v.1 j = 0 :=
    v.2 j (fun he => hi (hji.trans (congrArg (· + 1) he)))
  fin_cases i
  · simp [contraction]
  · have hz : v.1 0 = 0 := hs 0 (by decide)
    simp [contraction, hz]
  · have hz : v.1 0 = 0 := hs 0 (by decide)
    simp [contraction, hz]
  · have hz : v.1 2 = 0 := hs 2 (by decide)
    simp [contraction, hz]
  · have hz : v.1 0 = 0 := hs 0 (by decide)
    simp [contraction, hz]
  · have hz : v.1 4 = 0 := hs 4 (by decide)
    simp [contraction, hz]
  · have hz : v.1 4 = 0 := hs 4 (by decide)
    simp [contraction, hz]
  · have hz : v.1 6 = 0 := hs 6 (by decide)
    simp [contraction, hz]
  · have hz : v.1 0 = 0 := hs 0 (by decide)
    simp [contraction, hz]
  · have hz : v.1 8 = 0 := hs 8 (by decide)
    simp [contraction, hz]
  · have hz : v.1 8 = 0 := hs 8 (by decide)
    simp [contraction, hz]
  · have hz : v.1 10 = 0 := hs 10 (by decide)
    simp [contraction, hz]
  · have hz : v.1 8 = 0 := hs 8 (by decide)
    simp [contraction, hz]
  · have hz : v.1 12 = 0 := hs 12 (by decide)
    simp [contraction, hz]
  · have hz : v.1 12 = 0 := hs 12 (by decide)
    simp [contraction, hz]
  · have hz : v.1 14 = 0 := hs 14 (by decide)
    simp [contraction, hz]
theorem terminalProjection_eq_zero (n : ℕ) (v : graded k (n+1)) :
    terminalProjection v.1 = 0 := by
  have hv : v.1 0 = 0 := v.2 0 (by simp [degree])
  simp [terminalProjection, hv]

/-- Every genuine positive-degree Koszul cycle has an explicit preimage. -/
theorem exact_positive (n : ℕ) (v : graded k (n+1))
    (hv : gradedDifferential k n v = 0) :
    ∃ w : graded k (n+2), gradedDifferential k (n+1) w = v := by
  refine ⟨⟨contraction v.1, contraction_mem (n+1) v⟩, ?_⟩
  apply Subtype.ext
  change differential (contraction v.1) = v.1
  have h := contraction_identity v.1
  have hd : differential v.1 = 0 := congrArg Subtype.val hv
  rw [hd, terminalProjection_eq_zero n v] at h
  simpa only [contraction_zero, add_zero, sub_zero] using h

theorem degree_le_four (i : Fin 16) : degree i ≤ 4 := by
  fin_cases i <;> decide

instance graded_vanish (k : Type) [Field k] (n : ℕ) :
    Subsingleton (graded k (n+5)) := by
  refine ⟨fun v w => ?_⟩
  apply Subtype.ext
  funext i
  have hi : degree i ≠ n+5 := by have h := degree_le_four i; omega
  rw [v.2 i hi, w.2 i hi]

end NSP3.TorSpike.Koszul
