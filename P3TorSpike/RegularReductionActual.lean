import P3TorSpike.RegularReductionComparison
import P3TorSpike.SemigroupTorKoszul

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NSP3.TorSpike.RegularReduction
open CategoryTheory
open Koszul
variable (k : Type) [Field k] (m a b c : ℕ)

theorem semigroupTailGenerators_eq :
    tailGenerators (SemigroupRing k m a b c) (semigroupKoszulGenerators k m a b c) =
      semigroupParameters k m a b c := by
  funext i
  fin_cases i <;> rfl

def semigroupBaseH1ConeIso :
    (semigroupKoszulComplex k m a b c).sc' 2 1 0 ≅ semigroupConeH1Complex k m a b c := by
  have e := baseH1ConeIso k (SemigroupRing k m a b c) (semigroupKoszulGenerators k m a b c)
  rw [semigroupTailGenerators_eq k m a b c] at e
  exact e

def semigroupBaseH2ConeIso :
    (semigroupKoszulComplex k m a b c).sc' 3 2 1 ≅ semigroupConeH2Complex k m a b c := by
  have e := baseH2ConeIso k (SemigroupRing k m a b c) (semigroupKoszulGenerators k m a b c)
  rw [semigroupTailGenerators_eq k m a b c] at e
  exact e

def semigroupBaseH3ConeIso :
    (semigroupKoszulComplex k m a b c).sc' 4 3 2 ≅ semigroupConeH3Complex k m a b c := by
  have e := baseH3ConeIso k (SemigroupRing k m a b c) (semigroupKoszulGenerators k m a b c)
  rw [semigroupTailGenerators_eq k m a b c] at e
  exact e

/-- Actual four-generator Koszul H1 is the actual reduced three-generator H1. -/
def semigroupKoszulH1Equiv :
    (semigroupKoszulComplex k m a b c).homology 1 ≃ₗ[k]
      (threeH1Complex k (Reduction k m a b c) (reducedGenerator k m a b c)).homology :=
  ((semigroupKoszulComplex k m a b c).homologyIsoSc' 2 1 0 (by simp) (by simp)).toLinearEquiv.trans
    ((ShortComplex.homologyMapIso (semigroupBaseH1ConeIso k m a b c)).toLinearEquiv.trans
      (semigroupH1Equiv k m a b c))

/-- Actual four-generator Koszul H2 is the actual reduced three-generator H2. -/
def semigroupKoszulH2Equiv :
    (semigroupKoszulComplex k m a b c).homology 2 ≃ₗ[k]
      (threeH2Complex k (Reduction k m a b c) (reducedGenerator k m a b c)).homology :=
  ((semigroupKoszulComplex k m a b c).homologyIsoSc' 3 2 1 (by simp) (by simp)).toLinearEquiv.trans
    ((ShortComplex.homologyMapIso (semigroupBaseH2ConeIso k m a b c)).toLinearEquiv.trans
      (semigroupH2Equiv k m a b c))

/-- Actual four-generator Koszul H3 is the actual reduced common-annihilator kernel. -/
def semigroupKoszulH3Equiv :
    (semigroupKoszulComplex k m a b c).homology 3 ≃ₗ[k]
      LinearMap.ker (threeD3 k (Reduction k m a b c) (reducedGenerator k m a b c)) :=
  ((semigroupKoszulComplex k m a b c).homologyIsoSc' 4 3 2 (by simp) (by simp)).toLinearEquiv.trans
    ((ShortComplex.homologyMapIso (semigroupBaseH3ConeIso k m a b c)).toLinearEquiv.trans
      (semigroupH3Equiv k m a b c))

end NSP3.TorSpike.RegularReduction
