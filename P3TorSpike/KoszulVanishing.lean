import P3TorSpike.SemigroupTorKoszul
import P3TorSpike.RegularReductionComparison

noncomputable section
namespace NSP3.TorSpike
open CategoryTheory

/-- All actual Tor objects vanish from degree four, by the proved Koszul
resolution and the regular multiplicity monomial. -/
theorem torModule_isZero_from_four (k : Type) [Field k] (m a b c n : ℕ) (hn : 4 ≤ n) :
    CategoryTheory.Limits.IsZero
      ((ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
        (torModule k m a b c n)) := by
  have hz := RegularReduction.baseHomology_isZero_ge4 k (SemigroupRing k m a b c)
    (semigroupKoszulGenerators k m a b c) (monomial_mul_injective k (generator m a b c 0)) n hn
  exact CategoryTheory.Limits.IsZero.of_iso hz (torKoszulFieldIso k m a b c n)

end NSP3.TorSpike
