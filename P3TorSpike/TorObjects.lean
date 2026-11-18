import P3TorSpike.SemigroupRing
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Projective

noncomputable section
namespace NSP3.TorSpike
open CategoryTheory CategoryTheory.MonoidalCategory

def polynomialModule (k : Type) [Field k] (m a b c : ℕ) :
    Module (PolynomialRing k) (SemigroupRing k m a b c) :=
  Module.compHom (SemigroupRing k m a b c) (polynomialMap k m a b c).toRingHom

def ringModule (k : Type) [Field k] (m a b c : ℕ) : ModuleCat (PolynomialRing k) := by
  letI := polynomialModule k m a b c
  exact ModuleCat.of (PolynomialRing k) (SemigroupRing k m a b c)

def residueModule (k : Type) [Field k] : ModuleCat (PolynomialRing k) := by
  letI : Module (PolynomialRing k) k := Module.compHom k MvPolynomial.constantCoeff
  exact ModuleCat.of (PolynomialRing k) k

/-- The actual categorical Tor, with P acting through the polynomial map on R
and through the zero-variable augmentation on k. This defines no Betti identity. -/
def torModule (k : Type) [Field k] (m a b c n : ℕ) : ModuleCat (PolynomialRing k) :=
  ((CategoryTheory.Tor (ModuleCat (PolynomialRing k)) n).obj
    (ringModule k m a b c)).obj (residueModule k)

/-- Scalar restriction along k -> P gives the genuine k-vector space underlying Tor. -/
def torVectorModule (k : Type) [Field k] (m a b c n : ℕ) :
    Module k (torModule k m a b c n) :=
  Module.compHom (torModule k m a b c n) (algebraMap k (PolynomialRing k))

/-- Cardinal dimension is used until finiteness has been proved. -/
def torDimension (k : Type) [Field k] (m a b c n : ℕ) : Cardinal := by
  letI := torVectorModule k m a b c n
  exact Module.rank k (torModule k m a b c n)

/-- A first actual homological bridge: Tor_0 agrees with the tensor product. -/
def torZeroIsoTensor (k : Type) [Field k] (m a b c : ℕ) :
    torModule k m a b c 0 ≅
      (ringModule k m a b c ⊗ residueModule k) :=
  (Functor.leftDerivedZeroIsoSelf
    ((tensoringLeft (ModuleCat (PolynomialRing k))).obj (ringModule k m a b c))).app
      (residueModule k)

end NSP3.TorSpike
