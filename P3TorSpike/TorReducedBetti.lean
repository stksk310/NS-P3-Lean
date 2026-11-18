import P3TorSpike.RegularReductionActual
import P3TorSpike.ReductionHomology
import P3TorSpike.KoszulVanishing
import P3TorSpike.TorBettiDefinitions

noncomputable section
namespace NSP3.TorSpike
open CategoryTheory

def torReducedH1Equiv (k : Type) [Field k] (m a b c : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
        (torModule k m a b c 1) ≃ₗ[k]
      (threeH1Complex k (Reduction k m a b c) (reducedGenerator k m a b c)).homology :=
  (torKoszulFieldIso k m a b c 1).toLinearEquiv.trans
    (RegularReduction.semigroupKoszulH1Equiv k m a b c)

def torReducedH2Equiv (k : Type) [Field k] (m a b c : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
        (torModule k m a b c 2) ≃ₗ[k]
      (threeH2Complex k (Reduction k m a b c) (reducedGenerator k m a b c)).homology :=
  (torKoszulFieldIso k m a b c 2).toLinearEquiv.trans
    (RegularReduction.semigroupKoszulH2Equiv k m a b c)

def torReducedH3Equiv (k : Type) [Field k] (m a b c : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
        (torModule k m a b c 3) ≃ₗ[k]
      LinearMap.ker (threeD3 k (Reduction k m a b c) (reducedGenerator k m a b c)) :=
  (torKoszulFieldIso k m a b c 3).toLinearEquiv.trans
    (RegularReduction.semigroupKoszulH3Equiv k m a b c)

theorem torBetti_three (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    torBetti k m a b c 3 = NSP3.V03.pseudoFrobeniusType m a b c :=
  (torReducedH3Equiv k m a b c).finrank_eq.trans (reducedTop_finrank k m a b c h)

theorem torBetti_middle (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    torBetti k m a b c 2 + 1 = torBetti k m a b c 1 + torBetti k m a b c 3 := by
  have he₁ := (torReducedH1Equiv k m a b c).finrank_eq
  have he₂ := (torReducedH2Equiv k m a b c).finrank_eq
  have he := reduced_middle_identity k m a b c h
  have he₃ := torBetti_three k m a b c h
  change torBetti k m a b c 1 = _ at he₁
  change torBetti k m a b c 2 = _ at he₂
  omega

theorem torBetti_from_four (k : Type) [Field k] (m a b c n : ℕ) (hn : 4 ≤ n) :
    torBetti k m a b c n = 0 := by
  letI := ModuleCat.isZero_iff_subsingleton.mp (torModule_isZero_from_four k m a b c n hn)
  exact Module.finrank_zero_of_subsingleton

theorem tor_finite_all (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (n : ℕ) :
    Module.Finite k ((ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
      (torModule k m a b c n)) := by
  letI := reduction_finite k m a b c h.positive h.coprime
  rcases n with _ | _ | _ | _ | n
  · exact torZero_finite k m a b c h
  · letI := threeH1_finite k (Reduction k m a b c) (reducedGenerator k m a b c)
    exact Module.Finite.of_surjective (torReducedH1Equiv k m a b c).symm.toLinearMap
      (torReducedH1Equiv k m a b c).symm.surjective
  · letI := threeH2_finite k (Reduction k m a b c) (reducedGenerator k m a b c)
    exact Module.Finite.of_surjective (torReducedH2Equiv k m a b c).symm.toLinearMap
      (torReducedH2Equiv k m a b c).symm.surjective
  · exact Module.Finite.of_surjective (torReducedH3Equiv k m a b c).symm.toLinearMap
      (torReducedH3Equiv k m a b c).symm.surjective
  · letI := ModuleCat.isZero_iff_subsingleton.mp
      (torModule_isZero_from_four k m a b c (n+4) (by omega))
    infer_instance

/-- Cardinal dimension agrees with the finite numerical Betti invariant,
after the actual all-degree finiteness proof. -/
theorem torDimension_eq_torBetti (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (n : ℕ) :
    torDimension k m a b c n = (torBetti k m a b c n : Cardinal) := by
  letI := torVectorModule k m a b c n
  letI : Module.Finite k (torModule k m a b c n) := tor_finite_all k m a b c h n
  exact (Module.finrank_eq_rank k (torModule k m a b c n)).symm

end NSP3.TorSpike
