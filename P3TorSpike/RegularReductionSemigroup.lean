import P3TorSpike.RegularReductionHigher
import P3TorSpike.SocleBasic

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NSP3.TorSpike.RegularReduction
open CategoryTheory

variable (k : Type) [Field k] (m a b c : ℕ)

/-- The actual three nonmultiplicity monomials in k[S]. -/
def semigroupParameters : Fin 3 → SemigroupRing k m a b c :=
  fun i => monomial k (nonmultiplicityGenerator m a b c i)

/-- The actual regular multiplicity monomial. -/
def semigroupMultiplicity : SemigroupRing k m a b c := monomial k (generator m a b c 0)

theorem semigroupMultiplicity_regular :
    Function.Injective (multiply k (SemigroupRing k m a b c) (semigroupMultiplicity k m a b c)) :=
  monomial_mul_injective k _

def semigroupConeH1Complex : ShortComplex (ModuleCat.{0} k) :=
  coneShortComplex (threeH1Complex k (SemigroupRing k m a b c) (semigroupParameters k m a b c))
    (multiplyH1 k (SemigroupRing k m a b c) (semigroupMultiplicity k m a b c)
      (semigroupParameters k m a b c))
    (0 : SemigroupRing k m a b c →ₗ[k] (Fin 0 → SemigroupRing k m a b c)) (by rfl)

def semigroupConeH2Complex : ShortComplex (ModuleCat.{0} k) :=
  coneShortComplex (threeH2Complex k (SemigroupRing k m a b c) (semigroupParameters k m a b c))
    (multiplyH2 k (SemigroupRing k m a b c) (semigroupMultiplicity k m a b c)
      (semigroupParameters k m a b c))
    (threeD1 k (SemigroupRing k m a b c) (semigroupParameters k m a b c))
    (threeD1_comp_threeD2 k (SemigroupRing k m a b c) (semigroupParameters k m a b c))

def semigroupConeH3Complex : ShortComplex (ModuleCat.{0} k) :=
  coneShortComplex (threeH3Complex k (SemigroupRing k m a b c) (semigroupParameters k m a b c))
    (multiplyH3 k (SemigroupRing k m a b c) (semigroupMultiplicity k m a b c)
      (semigroupParameters k m a b c))
    (threeD2 k (SemigroupRing k m a b c) (semigroupParameters k m a b c))
    (threeD2_comp_threeD3 k (SemigroupRing k m a b c) (semigroupParameters k m a b c))

/-- Genuine degree-one homology comparison, using actual monomial regularity. -/
def semigroupH1Equiv :
    (semigroupConeH1Complex k m a b c).homology ≃ₗ[k]
    (threeH1Complex k (Reduction k m a b c) (reducedGenerator k m a b c)).homology :=
  regularH1Equiv k (SemigroupRing k m a b c) (semigroupMultiplicity k m a b c)
    (semigroupParameters k m a b c) (semigroupMultiplicity_regular k m a b c)

/-- Genuine degree-two homology comparison, using actual monomial regularity. -/
def semigroupH2Equiv :
    (semigroupConeH2Complex k m a b c).homology ≃ₗ[k]
    (threeH2Complex k (Reduction k m a b c) (reducedGenerator k m a b c)).homology :=
  regularH2Equiv k (SemigroupRing k m a b c) (semigroupMultiplicity k m a b c)
    (semigroupParameters k m a b c) (semigroupMultiplicity_regular k m a b c)

/-- Genuine degree-three comparison with the actual reduced top kernel. -/
def semigroupH3Equiv :
    (semigroupConeH3Complex k m a b c).homology ≃ₗ[k]
      LinearMap.ker (threeD3 k (Reduction k m a b c) (reducedGenerator k m a b c)) :=
  (regularH3Equiv k (SemigroupRing k m a b c) (semigroupMultiplicity k m a b c)
    (semigroupParameters k m a b c) (semigroupMultiplicity_regular k m a b c)).trans
    (threeH3EquivKer k (Reduction k m a b c) (reducedGenerator k m a b c))

end NSP3.TorSpike.RegularReduction
