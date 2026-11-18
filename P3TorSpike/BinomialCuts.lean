import P3TorSpike.BinomialConormal

noncomputable section
namespace NSP3.TorSpike

/-- Positive four-generator weights make every nonzero context strictly increase degree. -/
theorem factorWeight_pos (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (d : Fact4) (hd : d ≠ 0) : 0 < factorWeight m a b c d := by
  rw [← CommonCard.degree_fourCoordinates]
  apply (CommonCard.degree_pos_iff _ (CommonCard.generators_positive m a b c h) _).mpr
  intro hz
  apply hd
  apply fourCoordinates.injective
  exact hz.trans (show fourCoordinates 0 = 0 from by ext i; fin_cases i <;> rfl).symm

theorem factor_generated_weight (m a b c : ℕ) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R) {u v : Fact4} (huv : GeneratedAddRel R u v) :
    factorWeight m a b c u = factorWeight m a b c v :=
  (hR u v).mp ((generatedAddRel_four_iff R u v).mp huv)

/-- An edge cannot occur in a derivation at strictly smaller numerical weight. -/
theorem factor_generated_erase_lower (m a b c : ℕ) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R) (e : Fact4 × Fact4) {u v : Fact4}
    (huv : GeneratedAddRel R u v) :
    factorWeight m a b c u < factorWeight m a b c e.1 → GeneratedAddRel (R.erase e) u v := by
  classical
  induction huv with
  | edge hf =>
    intro hl
    exact .edge (Finset.mem_erase.mpr ⟨by intro he; subst e; exact (Nat.lt_irrefl _ hl), hf⟩)
  | refl u => intro _; exact .refl u
  | symm hh ih =>
    intro hl
    exact .symm (ih (by rw [factor_generated_weight m a b c R hR hh]; exact hl))
  | trans hh₁ hh₂ ih₁ ih₂ =>
    intro hl
    exact .trans (ih₁ hl) (ih₂ (by rw [← factor_generated_weight m a b c R hR hh₁]; exact hl))
  | context hh d ih =>
    intro hl
    exact .context (ih (by rw [factorWeight_add] at hl; omega)) d

def factorCut (k : Type) [Field k] (m a b c : ℕ) (R : Finset (Fact4 × Fact4))
    (e : Fact4 × Fact4) (u : Fact4) : k := by
  classical
  exact if factorWeight m a b c u = factorWeight m a b c e.1 ∧
    GeneratedAddRel (R.erase e) e.1 u then 1 else 0

theorem factorCut_eq_of_generated (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R)
    (e : Fact4 × Fact4) {u v : Fact4} (huv : GeneratedAddRel (R.erase e) u v) :
    factorCut k m a b c R e u = factorCut k m a b c R e v := by
  classical
  have hweight := factor_generated_weight m a b c R hR
    (CommonCard.generated_mono _ _ (Finset.erase_subset _ _) huv)
  have hconn : GeneratedAddRel (R.erase e) e.1 u ↔ GeneratedAddRel (R.erase e) e.1 v :=
    ⟨fun hh => .trans hh huv, fun hh => .trans hh (.symm huv)⟩
  simp only [factorCut, hweight, hconn]

theorem factorCut_positive_context (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R) (e : Fact4 × Fact4)
    {u v : Fact4} (huv : GeneratedAddRel R u v) (d : Fact4) (hd : d ≠ 0) :
    factorCut k m a b c R e (u + d) = factorCut k m a b c R e (v + d) := by
  classical
  have hw := factor_generated_weight m a b c R hR huv
  by_cases hu : factorWeight m a b c (u + d) = factorWeight m a b c e.1
  · have hp := factorWeight_pos m a b c h d hd
    have hl : factorWeight m a b c u < factorWeight m a b c e.1 := by
      rw [factorWeight_add] at hu
      omega
    exact factorCut_eq_of_generated k m a b c R hR e
      (.context (factor_generated_erase_lower m a b c R hR e huv hl) d)
  · have hv : factorWeight m a b c (v + d) ≠ factorWeight m a b c e.1 := by
      simpa only [factorWeight_add, ← hw] using hu
    simp [factorCut, hu, hv]

/-- A coefficient functional defined over every field, with a genuine component cut. -/
def binomialCut (k : Type) [Field k] (m a b c : ℕ) (R : Finset (Fact4 × Fact4))
    (e : Fact4 × Fact4) : PolynomialRing k →ₗ[k] k :=
  (Finsupp.linearCombination k (fun d => factorCut k m a b c R e (factExponent.symm d))).comp
    (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

@[simp] theorem binomialCut_factMonomial (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (e : Fact4 × Fact4) (u : Fact4) :
    binomialCut k m a b c R e (factMonomial k u) = factorCut k m a b c R e u := by
  change Finsupp.linearCombination k _ (Finsupp.single (factExponent u) 1) = _
  simp only [Finsupp.linearCombination_single, AddEquiv.symm_apply_apply, one_smul]

theorem binomialCut_other_relation (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R)
    (e f : Fact4 × Fact4) (hf : f ∈ R) (hne : f ≠ e) :
    binomialCut k m a b c R e (relationBinomial k f) = 0 := by
  rw [relationBinomial, map_sub, binomialCut_factMonomial, binomialCut_factMonomial]
  exact sub_eq_zero.mpr (factorCut_eq_of_generated k m a b c R hR e
    (.edge (Finset.mem_erase.mpr ⟨hne, hf⟩)))

theorem binomialCut_own_relation (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R)
    (e : Fact4 × Fact4) (he : e ∈ R) (hne : ¬ GeneratedAddRel (R.erase e) e.1 e.2) :
    binomialCut k m a b c R e (relationBinomial k e) = 1 := by
  classical
  have hw := factor_generated_weight m a b c R hR (.edge he)
  rw [relationBinomial, map_sub, binomialCut_factMonomial, binomialCut_factMonomial]
  simp [factorCut, hne, hw, GeneratedAddRel.refl]

theorem binomialCut_context_relation (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R) (e f : Fact4 × Fact4) (hf : f ∈ R)
    (d : Fact4) (hd : d ≠ 0) :
    binomialCut k m a b c R e (factMonomial k d * relationBinomial k f) = 0 := by
  rw [relationBinomial, mul_sub, ← factMonomial_add, ← factMonomial_add,
    map_sub, binomialCut_factMonomial, binomialCut_factMonomial]
  apply sub_eq_zero.mpr
  have hcomm (u v : Fact4) : u + v = v + u := by
    apply factExponent.injective
    simp only [map_add, add_comm]
  simpa only [hcomm d f.1, hcomm d f.2] using factorCut_positive_context k m a b c h R hR e (.edge hf) d hd

theorem factor_add_ne_zero (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (u v : Fact4) (hu : u ≠ 0) : u + v ≠ 0 := by
  intro hh
  have hw := congrArg (factorWeight m a b c) hh
  have hp := factorWeight_pos m a b c h u hu
  rw [factorWeight_add] at hw
  have hz : factorWeight m a b c 0 = 0 := by
    change 0 * m + (a * 0 + b * 0 + c * 0) = 0
    omega
  rw [hz] at hw
  omega

/-- Every positive monomial times any genuine relation is killed by a component cut. -/
theorem binomialCut_context_mem (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R) (e : Fact4 × Fact4)
    (p : PolynomialRing k) (hp : p ∈ binomialIdeal k R) :
    ∀ d : Fact4, d ≠ 0 → binomialCut k m a b c R e (factMonomial k d * p) = 0 := by
  change p ∈ Submodule.span (PolynomialRing k) _ at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨f, hf, rfl⟩ := hp
    exact binomialCut_context_relation k m a b c h R hR e f hf
  | zero => intro d hd; simp
  | add p q hp hq ihp ihq =>
    intro d hd
    simp only [mul_add, map_add, ihp d hd, ihq d hd, add_zero]
  | smul q p hp ih =>
    intro d hd
    change binomialCut k m a b c R e (factMonomial k d * (q * p)) = 0
    induction q using MvPolynomial.induction_on' with
    | monomial z r =>
      let u : Fact4 := factExponent.symm z
      have hu : (MvPolynomial.monomial z r : PolynomialRing k) = r • factMonomial k u := by
        simp [factMonomial, u, MvPolynomial.smul_monomial]
      rw [hu, smul_mul_assoc, mul_smul_comm, ← mul_assoc, ← factMonomial_add, map_smul,
        ih (d + u) (factor_add_ne_zero m a b c h d u hd), smul_zero]
    | add q₁ q₂ iha ihb =>
      simp only [add_mul, mul_add, map_add, iha, ihb, add_zero]

@[simp] theorem factExponent_zero : factExponent 0 = 0 := by
  ext i; fin_cases i <;> rfl

@[simp] theorem factExponent_eq_zero (u : Fact4) : factExponent u = 0 ↔ u = 0 := by
  constructor
  · intro hu; apply factExponent.injective; exact hu.trans factExponent_zero.symm
  · rintro rfl; exact factExponent_zero

@[simp] theorem factMonomial_zero (k : Type) [Field k] : factMonomial k 0 = 1 := by
  simp [factMonomial]

@[simp] theorem polynomialAugmentation_factMonomial (k : Type) [Field k] (u : Fact4) :
    polynomialAugmentation k (factMonomial k u) = if u = 0 then 1 else 0 := by
  simp [polynomialAugmentation, factMonomial, MvPolynomial.constantCoeff_monomial]

/-- On the true kernel, each cut transforms polynomial scalar multiplication through augmentation. -/
theorem binomialCut_mul_mem (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R) (e : Fact4 × Fact4)
    (p : PolynomialRing k) (hp : p ∈ binomialIdeal k R) (q : PolynomialRing k) :
    binomialCut k m a b c R e (q * p) =
      polynomialAugmentation k q * binomialCut k m a b c R e p := by
  induction q using MvPolynomial.induction_on' with
  | monomial z r =>
    let u : Fact4 := factExponent.symm z
    have hu : (MvPolynomial.monomial z r : PolynomialRing k) = r • factMonomial k u := by
      simp [factMonomial, u, MvPolynomial.smul_monomial]
    rw [hu, smul_mul_assoc, map_smul, map_smul, polynomialAugmentation_factMonomial]
    by_cases hz : u = 0
    · rw [if_pos hz, hz]
      simp
    · rw [if_neg hz, binomialCut_context_mem k m a b c h R hR e p hp u hz]
      simp
  | add q₁ q₂ iha ihb => simp only [add_mul, map_add, iha, ihb]

end NSP3.TorSpike
