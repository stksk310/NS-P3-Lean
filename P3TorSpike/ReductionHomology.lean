import P3TorSpike.ReductionComplex
import P3TorSpike.AugmentedQuotient
import P3TorSpike.SocleBasis
import P3TorSpike.Augmentation

noncomputable section
namespace NSP3.TorSpike

def reducedAugmentation (k : Type) [Field k] (m a b c : ℕ) (hm : 0 < m) :
    Reduction k m a b c →ₐ[k] k := by
  have hi : multiplicityIdeal k m a b c ≤
      RingHom.ker (augmentation k m a b c).toRingHom := by
    rw [multiplicityIdeal, Ideal.span_le]
    rintro f (rfl : f = monomial k (generator m a b c 0))
    change augmentation k m a b c (monomial k (generator m a b c 0)) = 0
    rw [augmentation_monomial]
    simp [generator, Nat.ne_of_gt hm]
  exact Ideal.Quotient.liftₐ _ (augmentation k m a b c) (fun _ hx => hi hx)

@[simp] theorem reducedAugmentation_mk (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (f : SemigroupRing k m a b c) :
    reducedAugmentation k m a b c hm (reductionMap k m a b c f) =
      augmentation k m a b c f := rfl

@[simp] theorem reducedAugmentation_generator (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (i : Fin 3) :
    reducedAugmentation k m a b c h.positive (reducedGenerator k m a b c i) = 0 := by
  rw [reducedGenerator, reducedAugmentation_mk, augmentation_monomial]
  have hp : 0 < (nonmultiplicityGenerator m a b c i).val := by
    fin_cases i <;> simp [nonmultiplicityGenerator, generator] <;>
      first | exact lt_of_lt_of_le h.positive h.least_a
            | exact lt_of_lt_of_le h.positive h.least_b
            | exact lt_of_lt_of_le h.positive h.least_c
  simp [Nat.ne_of_gt hp]

theorem reducedMultiplicity_zero (k : Type) [Field k] (m a b c : ℕ) :
    reductionMap k m a b c (monomial k (generator m a b c 0)) = 0 := by
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The actual degree-zero quotient of the reduced Koszul complex. -/
def reducedH0Equiv (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    (Reduction k m a b c ⧸ LinearMap.range
      (threeD1 k (Reduction k m a b c) (reducedGenerator k m a b c))) ≃ₗ[k] k := by
  let A := Reduction k m a b c
  let u := reducedGenerator k m a b c
  let f := (reductionMap k m a b c).comp (polynomialMap k m a b c)
  let ε := reducedAugmentation k m a b c h.positive
  let J := threeImageIdeal k A u
  have hs : Function.Surjective f :=
    (Ideal.Quotient.mkₐ_surjective k _).comp (polynomialMap_surjective k m a b c)
  have hJ : ∀ x ∈ J, ε x = 0 := by
    have hεu : ∀ i, ε (u i) = 0 := reducedAugmentation_generator k m a b c h
    rintro _ ⟨v, rfl⟩
    change ε (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) = 0
    simp only [map_add, map_mul]
    simp [hεu]
  have hX : ∀ i, f (MvPolynomial.X i) ∈ J := by
    intro i
    change reductionMap k m a b c ((polynomialMap k m a b c) (MvPolynomial.X i)) ∈ J
    rw [polynomialMap_X]
    fin_cases i
    · change reductionMap k m a b c (monomial k (generator m a b c 0)) ∈ J
      rw [reducedMultiplicity_zero]
      exact J.zero_mem
    · exact threeGenerator_mem_image k A u 0
    · exact threeGenerator_mem_image k A u 1
    · exact threeGenerator_mem_image k A u 2
  exact (variablesQuotientEquiv k A f hs ε J hJ hX).toLinearEquiv

theorem reducedH0_finrank (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    Module.finrank k (Reduction k m a b c ⧸ LinearMap.range
      (threeD1 k (Reduction k m a b c) (reducedGenerator k m a b c))) = 1 :=
  (reducedH0Equiv k m a b c h).finrank_eq.trans (by simp)

theorem reducedD3_ker_eq_socle (k : Type) [Field k] (m a b c : ℕ) :
    LinearMap.ker (threeD3 k (Reduction k m a b c) (reducedGenerator k m a b c)) =
      socle k m a b c := by
  ext v
  exact mem_threeD3_ker k _ _ v

theorem reducedTop_finrank (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    Module.finrank k (LinearMap.ker
      (threeD3 k (Reduction k m a b c) (reducedGenerator k m a b c))) =
      NSP3.V03.pseudoFrobeniusType m a b c := by
  rw [reducedD3_ker_eq_socle]
  exact socle_finrank_eq_type k m a b c h

/-- An unconditional identity for the genuine homology of the reduced complex.
The comparison with categorical Tor is a separate subsequent theorem. -/
theorem reduced_middle_identity (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    1 + Module.finrank k
      (threeH2Complex k (Reduction k m a b c) (reducedGenerator k m a b c)).homology =
    Module.finrank k
      (threeH1Complex k (Reduction k m a b c) (reducedGenerator k m a b c)).homology +
      NSP3.V03.pseudoFrobeniusType m a b c := by
  letI := reduction_finite k m a b c h.positive h.coprime
  have he := three_euler k (Reduction k m a b c) (reducedGenerator k m a b c)
  rw [reducedH0_finrank k m a b c h, reducedTop_finrank k m a b c h] at he
  exact he

end NSP3.TorSpike
