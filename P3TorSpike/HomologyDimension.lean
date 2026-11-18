import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

noncomputable section
namespace NSP3.TorSpike
open CategoryTheory

/-- Dimension bookkeeping for actual categorical homology. -/
theorem shortComplex_homology_finrank (k : Type) [Field k]
    (S : ShortComplex (ModuleCat.{0} k))
    [Module.Finite k S.X₁] [Module.Finite k S.X₂] :
    Module.finrank k S.homology + Module.finrank k (LinearMap.range S.f.hom) +
      Module.finrank k (LinearMap.range S.g.hom) = Module.finrank k S.X₂ := by
  have he := S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  change Module.finrank k S.homology =
    Module.finrank k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) at he
  have hq := (LinearMap.range S.moduleCatToCycles).finrank_quotient_add_finrank
  have hr₁ := S.moduleCatToCycles.finrank_range_add_finrank_ker
  have hr₂ := S.f.hom.finrank_range_add_finrank_ker
  have hk : LinearMap.ker S.moduleCatToCycles = LinearMap.ker S.f.hom := by
    ext x
    change (⟨S.f.hom x, _⟩ : LinearMap.ker S.g.hom) = 0 ↔ S.f.hom x = 0
    exact Subtype.ext_iff
  have hg := S.g.hom.finrank_range_add_finrank_ker
  rw [hk] at hr₁
  omega

theorem shortComplex_homology_finite (k : Type) [Field k]
    (S : ShortComplex (ModuleCat.{0} k)) [Module.Finite k S.X₂] :
    Module.Finite k S.homology := by
  let e := S.moduleCatHomologyIso.toLinearEquiv
  haveI : Module.Finite k S.moduleCatLeftHomologyData.H :=
    (inferInstance : Module.Finite k
      (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles))
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

end NSP3.TorSpike
