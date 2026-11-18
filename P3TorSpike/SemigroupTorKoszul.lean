import P3TorSpike.KoszulResolution
import P3TorSpike.KoszulTensor
import P3TorSpike.KoszulScalarRestriction
import P3TorSpike.TensorResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace NSP3.TorSpike
open CategoryTheory

def semigroupKoszulGenerators (k : Type) [Field k] (m a b c : ℕ) :
    Fin 4 → SemigroupRing k m a b c := fun i => monomial k (generator m a b c i)

def semigroupKoszulComplex (k : Type) [Field k] (m a b c : ℕ) :
    ChainComplex (ModuleCat k) ℕ :=
  Koszul.baseComplex k (SemigroupRing k m a b c) (semigroupKoszulGenerators k m a b c)

/-- The categorical Tor of the actual semigroup algebra is computed by its
explicit four-variable Koszul complex. The polynomial resolution is proved. -/
def torKoszulFieldIso (k : Type) [Field k] (m a b c n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
        (torModule k m a b c n) ≅
      (semigroupKoszulComplex k m a b c).homology n := by
  letI := semigroupAlgebra k m a b c
  letI : IsScalarTower k (PolynomialRing k) (SemigroupRing k m a b c) :=
    IsScalarTower.of_algHom (polynomialMap k m a b c)
  let e₁ := torResolutionFieldIso k m a b c n (Koszul.resolution k)
  let F := (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).mapHomologicalComplex
    (ComplexShape.down ℕ)
  let e₂ := F.mapIso (Koszul.tensorComplexIso k (SemigroupRing k m a b c))
  let e₃ := Koszul.restrictBaseComplexIso k (SemigroupRing k m a b c)
    (Koszul.baseGenerators k (SemigroupRing k m a b c))
  have hgen : Koszul.baseGenerators k (SemigroupRing k m a b c) =
      semigroupKoszulGenerators k m a b c := by
    funext i
    exact polynomialMap_X k m a b c i
  let e := e₁ ≪≫ (HomologicalComplex.homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) n).mapIso
    (e₂ ≪≫ e₃)
  dsimp only [HomologicalComplex.homologyFunctor] at e
  simpa only [semigroupKoszulComplex, hgen] using e

end NSP3.TorSpike
