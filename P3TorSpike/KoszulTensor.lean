import P3TorSpike.KoszulBaseChange
import P3TorSpike.TorResolution

noncomputable section
namespace NSP3.TorSpike.Koszul
open CategoryTheory CategoryTheory.MonoidalCategory

variable (k A : Type) [Field k] [CommRing A] [Algebra (PolynomialRing k) A]

def tensorComplex : ChainComplex (ModuleCat (PolynomialRing k)) ℕ := by
  let F := (tensoringLeft (ModuleCat (PolynomialRing k))).obj
    (ModuleCat.of (PolynomialRing k) A)
  exact (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (complex k)

def tensorComplexIso :
    tensorComplex k A ≅ baseComplex (PolynomialRing k) A (baseGenerators k A) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (tensorGradedEquiv k A n).toModuleIso) ?_
  intro i j hij
  obtain rfl : j + 1 = i := hij
  simp only [tensorComplex, complex, baseComplex, Functor.mapHomologicalComplex,
    ChainComplex.of_d]
  exact ModuleCat.hom_ext (tensorDifferential_compat k A j)

end NSP3.TorSpike.Koszul
