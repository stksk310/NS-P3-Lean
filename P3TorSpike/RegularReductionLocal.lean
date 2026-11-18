import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Quotient.Basic

noncomputable section
namespace NSP3.TorSpike.RegularReduction
open CategoryTheory

variable {k : Type} [Field k]

/-- A concrete map of cycles, before taking homology quotients. -/
def cyclesMap {S T : ShortComplex (ModuleCat.{0} k)} (φ : S ⟶ T) :
    LinearMap.ker S.g.hom →ₗ[k] LinearMap.ker T.g.hom :=
  (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (by
    intro x
    change T.g (φ.τ₂ x.val) = 0
    have hc := congrArg (fun f : S.X₂ ⟶ T.X₃ => f x.val) φ.comm₂₃
    simpa [x.property] using hc)

@[simp] theorem cyclesMap_val {S T : ShortComplex (ModuleCat.{0} k)} (φ : S ⟶ T)
    (x : LinearMap.ker S.g.hom) : (cyclesMap φ x).val = φ.τ₂ x.val := rfl

theorem cyclesMap_boundaries {S T : ShortComplex (ModuleCat.{0} k)} (φ : S ⟶ T) :
    LinearMap.range S.moduleCatToCycles ≤
      Submodule.comap (cyclesMap φ) (LinearMap.range T.moduleCatToCycles) := by
  rintro x ⟨a,rfl⟩
  refine ⟨φ.τ₁ a,?_⟩
  apply Subtype.ext
  exact congrArg (fun f : S.X₁ ⟶ T.X₂ => f a) φ.comm₁₂

def quotientMap {S T : ShortComplex (ModuleCat.{0} k)} (φ : S ⟶ T) :
    (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) →ₗ[k]
      (LinearMap.ker T.g.hom ⧸ LinearMap.range T.moduleCatToCycles) :=
  Submodule.mapQ _ _ (cyclesMap φ) (cyclesMap_boundaries φ)

/-- Elementary cycle lifting and boundary reflection prove an equivalence of actual homology.
Neither hypothesis assumes any homology comparison. -/
def homologyEquiv {S T : ShortComplex (ModuleCat.{0} k)} (φ : S ⟶ T)
    (hlift : ∀ y : T.X₂, T.g y = 0 → ∃ x : S.X₂, S.g x = 0 ∧ φ.τ₂ x = y)
    (hreflect : ∀ x : S.X₂, S.g x = 0 →
      (∃ b : T.X₁, T.f b = φ.τ₂ x) → ∃ a : S.X₁, S.f a = x) :
    S.homology ≃ₗ[k] T.homology := by
  let F := quotientMap φ
  have hinj : Function.Injective F := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro z hz
      obtain ⟨x,rfl⟩ := (LinearMap.range S.moduleCatToCycles).mkQ_surjective z
      change F ((LinearMap.range S.moduleCatToCycles).mkQ x) = 0 at hz
      have hmem : cyclesMap φ x ∈ LinearMap.range T.moduleCatToCycles := by
        exact (Submodule.Quotient.mk_eq_zero _).mp hz
      obtain ⟨b,hb⟩ := hmem
      have hb' : T.f b = φ.τ₂ x.val := congrArg Subtype.val hb
      obtain ⟨a,ha⟩ := hreflect x.val x.property ⟨b,hb'⟩
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact ⟨a,Subtype.ext ha⟩
    · exact bot_le
  have hsurj : Function.Surjective F := by
    intro z
    obtain ⟨y,rfl⟩ := (LinearMap.range T.moduleCatToCycles).mkQ_surjective z
    obtain ⟨x,hx,hxy⟩ := hlift y.val y.property
    refine ⟨(LinearMap.range S.moduleCatToCycles).mkQ ⟨x,hx⟩,?_⟩
    change (LinearMap.range T.moduleCatToCycles).mkQ (cyclesMap φ ⟨x,hx⟩) =
      (LinearMap.range T.moduleCatToCycles).mkQ y
    congr 1
    exact Subtype.ext hxy
  exact S.moduleCatHomologyIso.toLinearEquiv |>.trans
    ((LinearEquiv.ofBijective F ⟨hinj,hsurj⟩).trans T.moduleCatHomologyIso.toLinearEquiv.symm)

end NSP3.TorSpike.RegularReduction
