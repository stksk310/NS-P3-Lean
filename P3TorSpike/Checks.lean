import P3TorSpike.TorZero
import P3TorSpike.AperyBasis

open NSP3 NSP3.TorSpike
noncomputable section

#check polynomialMap_surjective
#check monomial_mul_injective
#check reduction_finrank_eq_m
#check torModule
#check torZeroIsoTensor
#check torZeroEquivResidue
#check torDimension_zero
#check torZero_finite
#check torFinrank_zero

#print axioms polynomialMap_surjective
#print axioms monomial_mul_injective
#print axioms outside_apery_killed
#print axioms aperyVectors_span
#print axioms aperyVectors_independent
#print axioms reduction_finrank_eq_m
#print axioms augmentation_polynomialMap
#print axioms quotientTensorEquiv
#print axioms torZeroIsoTensor
#print axioms torZeroEquivResidue
#print axioms torDimension_zero
#print axioms torZero_finite
#print axioms torFinrank_zero

example : Module.finrank ℚ (Reduction ℚ 4 7 9 10)=4 :=
  reduction_finrank_eq_m ℚ 4 7 9 10 (by decide) (by decide)

example (k : Type) [Field k] (m a b c : ℕ) :
    reductionMap k m a b c (monomial k (generator m a b c 0))=0 := by
  change Ideal.Quotient.mk (multiplicityIdeal k m a b c) _=0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)
