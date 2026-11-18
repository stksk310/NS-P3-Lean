import P3TorSpike.KoszulBaseChange
import P3TorSpike.TorResolution

noncomputable section
namespace NSP3.TorSpike.Koszul
open CategoryTheory

variable (k A : Type) [Field k] [CommRing A] [Algebra k A]
  [Algebra (PolynomialRing k) A] [IsScalarTower k (PolynomialRing k) A]

def restrictBaseGradedEquiv (n : ℕ) :
    (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
        (ModuleCat.of (PolynomialRing k) (baseGraded (PolynomialRing k) A n)) ≃ₗ[k]
      baseGraded k A n where
  toFun v := ⟨v.val, v.property⟩
  invFun v := ⟨v.val, v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r v := by
    apply Subtype.ext
    funext i
    change ((algebraMap k (PolynomialRing k) r) • v.val) i = (r • v.val) i
    simp only [Pi.smul_apply, Algebra.smul_def]
    rw [← IsScalarTower.algebraMap_apply k (PolynomialRing k) A]

def restrictBaseComplexIso (u : Fin 4 → A) :
    restrictComplex k (baseComplex (PolynomialRing k) A u) ≅ baseComplex k A u := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (restrictBaseGradedEquiv k A n).toModuleIso) ?_
  intro i j hij
  obtain rfl : j + 1 = i := hij
  simp only [restrictComplex, baseComplex, Functor.mapHomologicalComplex, ChainComplex.of_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  rfl

end NSP3.TorSpike.Koszul
