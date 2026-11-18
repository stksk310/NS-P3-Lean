import P3TorSpike.SemigroupRing
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
namespace NSP3.TorSpike

/-- The actual exponent vector of a four-input factorization. -/
def factExponent : Fact4 ≃+ (Fin 4 →₀ ℕ) :=
  { toFun := fun u => Finsupp.equivFunOnFinite.symm (fourCoordinates u)
    invFun := fun v => fourCoordinates.symm (fun i => v i)
    left_inv := by intro u; simp
    right_inv := by intro v; ext i; simp
    map_add' := by intro u v; ext i; exact congrFun (fourCoordinates.map_add u v) i }

@[simp] theorem factExponent_apply (u : Fact4) (i : Fin 4) :
    factExponent u i = fourCoordinates u i := rfl

def factMonomial (k : Type) [Field k] (u : Fact4) : PolynomialRing k :=
  MvPolynomial.monomial (factExponent u) 1

@[simp] theorem factMonomial_add (k : Type) [Field k] (u v : Fact4) :
    factMonomial k (u + v) = factMonomial k u * factMonomial k v := by
  simp [factMonomial, MvPolynomial.monomial_mul, map_add]

theorem factMonomial_eq (k : Type) [Field k] (u : Fact4) :
    factMonomial k u = MvPolynomial.X 0 ^ u.1 * MvPolynomial.X 1 ^ u.2.x *
      MvPolynomial.X 2 ^ u.2.y * MvPolynomial.X 3 ^ u.2.z := by
  rw [factMonomial, MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp [Fin.prod_univ_succ, fourCoordinates, mul_assoc]

def factorElement (m a b c : ℕ) (u : Fact4) : Semigroup m a b c :=
  ⟨factorWeight m a b c u, (factorWeight_image m a b c _).mp ⟨u, rfl⟩⟩

theorem polynomialMap_factMonomial (k : Type) [Field k] (m a b c : ℕ) (u : Fact4) :
    polynomialMap k m a b c (factMonomial k u) = monomial k (factorElement m a b c u) := by
  rw [factMonomial_eq]
  simp only [map_mul, map_pow, polynomialMap_X]
  exact (monomial_factorization k m a b c _ u.1 u.2.x u.2.y u.2.z
    (by simp [factorElement, factorWeight, aperyWeight]; ring)).symm

def relationBinomial (k : Type) [Field k] (e : Fact4 × Fact4) : PolynomialRing k :=
  factMonomial k e.1 - factMonomial k e.2

def binomialIdeal (k : Type) [Field k] (R : Finset (Fact4 × Fact4)) :
    Ideal (PolynomialRing k) := Ideal.span (relationBinomial k '' (R : Set (Fact4 × Fact4)))

theorem binomial_mem_of_presentationRel (k : Type) [Field k]
    (R : Finset (Fact4 × Fact4)) {u v : Fact4} (h : PresentationRel R u v) :
    factMonomial k u - factMonomial k v ∈ binomialIdeal k R := by
  induction h with
  | edge he => exact Ideal.subset_span ⟨_, he, rfl⟩
  | refl u => simp
  | symm _ ih => simpa [sub_eq_add_neg, add_comm] using (binomialIdeal k R).neg_mem ih
  | trans _ _ ih₁ ih₂ =>
    convert (binomialIdeal k R).add_mem ih₁ ih₂ using 1 <;> abel
  | context _ d ih =>
    simpa [factMonomial_add, sub_mul] using (binomialIdeal k R).mul_mem_right (factMonomial k d) ih

theorem binomialIdeal_le_ker (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R) :
    binomialIdeal k R ≤ RingHom.ker (polynomialMap k m a b c).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨e, he, rfl⟩
  change polynomialMap k m a b c (relationBinomial k e) = 0
  change polynomialMap k m a b c (factMonomial k e.1 - factMonomial k e.2) = 0
  rw [map_sub, polynomialMap_factMonomial, polynomialMap_factMonomial]
  have hh := (hR e.1 e.2).mp (.edge he)
  have hs : factorElement m a b c e.1 = factorElement m a b c e.2 := Subtype.ext hh
  rw [hs, sub_self]

/-- A genuine factorization chosen for every element of the actual semigroup. -/
def chosenFactor (m a b c : ℕ) (s : Semigroup m a b c) : Fact4 :=
  Classical.choose ((factorWeight_image m a b c s.val).mpr s.property)

@[simp] theorem chosenFactor_weight (m a b c : ℕ) (s : Semigroup m a b c) :
    factorWeight m a b c (chosenFactor m a b c s) = s.val :=
  Classical.choose_spec ((factorWeight_image m a b c s.val).mpr s.property)

@[simp] theorem factorElement_chosenFactor (m a b c : ℕ) (s : Semigroup m a b c) :
    factorElement m a b c (chosenFactor m a b c s) = s :=
  Subtype.ext (chosenFactor_weight m a b c s)

/-- A k-linear monomial section; it need not preserve multiplication. -/
def normalSection (k : Type) [Field k] (m a b c : ℕ) :
    SemigroupRing k m a b c →ₗ[k] PolynomialRing k :=
  (Finsupp.linearCombination k (fun s => factMonomial k (chosenFactor m a b c s))).comp
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem normalSection_monomial (k : Type) [Field k] (m a b c : ℕ)
    (s : Semigroup m a b c) :
    normalSection k m a b c (monomial k s) = factMonomial k (chosenFactor m a b c s) := by
  change Finsupp.linearCombination k
    (fun s => factMonomial k (chosenFactor m a b c s)) (Finsupp.single s 1) = _
  simp only [Finsupp.linearCombination_single, one_smul]

theorem polynomial_sub_normalSection_mem (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R)
    (p : PolynomialRing k) :
    p - normalSection k m a b c (polynomialMap k m a b c p) ∈ binomialIdeal k R := by
  induction p using MvPolynomial.induction_on' with
  | monomial d r =>
    let u : Fact4 := factExponent.symm d
    have hu : (MvPolynomial.monomial d r : PolynomialRing k) = r • factMonomial k u := by
      simp [factMonomial, u, MvPolynomial.smul_monomial]
    rw [hu, map_smul, map_smul, ← smul_sub, polynomialMap_factMonomial,
      normalSection_monomial]
    apply ((binomialIdeal k R).restrictScalars k).smul_mem
    apply binomial_mem_of_presentationRel
    apply (hR _ _).mpr
    simp [factorElement]
  | add p q hp hq =>
    rw [map_add, map_add]
    convert (binomialIdeal k R).add_mem hp hq using 1 <;> abel

/-- The full polynomial kernel is generated by the supplied genuine finite monoid presentation,
    over every field. No characteristic-zero hypothesis or auxiliary kernel certificate is used. -/
theorem binomialIdeal_eq_ker (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R) :
    binomialIdeal k R = RingHom.ker (polynomialMap k m a b c).toRingHom := by
  apply le_antisymm (binomialIdeal_le_ker k m a b c R hR)
  intro p hp
  have hz : polynomialMap k m a b c p = 0 := hp
  have hm := polynomial_sub_normalSection_mem k m a b c R hR p
  simpa [hz] using hm

/-- An actual finite binomial generating family with the intrinsic minimum relation count. -/
theorem minimal_binomial_kernel_presentation (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    ∃ R : Finset (Fact4 × Fact4), IsFactorPresentation m a b c R ∧
      R.card = intrinsicRho (generatedSemigroup m a b c) ∧
      binomialIdeal k R = RingHom.ker (polynomialMap k m a b c).toRingHom := by
  obtain ⟨R, hR, hc⟩ := minimumFourInputRelations_attained m a b c h.positive h.coprime
  exact ⟨R, hR, hc.trans (literature_rho_identification m a b c h).symm,
    binomialIdeal_eq_ker k m a b c R hR⟩

end NSP3.TorSpike
