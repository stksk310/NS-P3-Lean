import P3TorSpike.TorObjects
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

noncomputable section
namespace NSP3.TorSpike
open CategoryTheory CategoryTheory.MonoidalCategory

def tensorResolutionComplex (k : Type) [Field k] (m a b c : ℕ)
    (Q : ProjectiveResolution (residueModule k)) :
    ChainComplex (ModuleCat (PolynomialRing k)) ℕ := by
  let F := (tensoringLeft (ModuleCat (PolynomialRing k))).obj (ringModule k m a b c)
  exact (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex

/-- Computation of the genuine categorical Tor using a supplied *proved*
projective resolution. This is instantiated with the concrete Koszul resolution. -/
def torResolutionIso (k : Type) [Field k] (m a b c n : ℕ)
    (Q : ProjectiveResolution (residueModule k)) :
    torModule k m a b c n ≅ (tensorResolutionComplex k m a b c Q).homology n :=
  Q.isoLeftDerivedObj
    ((tensoringLeft (ModuleCat (PolynomialRing k))).obj (ringModule k m a b c)) n

def restrictComplex (k : Type) [Field k]
    (C : ChainComplex (ModuleCat.{0} (PolynomialRing k)) ℕ) :
    ChainComplex (ModuleCat.{0} k) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj C

def restrictHomologyIso (k : Type) [Field k]
    (C : ChainComplex (ModuleCat.{0} (PolynomialRing k)) ℕ) (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj (C.homology n) ≅
      (restrictComplex k C).homology n :=
  ((C.sc n).mapHomologyIso
    (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k)))).symm

def torResolutionFieldIso (k : Type) [Field k] (m a b c n : ℕ)
    (Q : ProjectiveResolution (residueModule k)) :
    (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
        (torModule k m a b c n) ≅
      (restrictComplex k (tensorResolutionComplex k m a b c Q)).homology n :=
  (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).mapIso
      (torResolutionIso k m a b c n Q) ≪≫
    restrictHomologyIso k _ n

end NSP3.TorSpike
