import Mathlib

noncomputable section
namespace NSP3.TorSpike

section AugmentationFibre
variable {k A M : Type} [Field k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- The actual augmentation submodule of an A-module. -/
def augmentationSubmodule (ε : A →ₐ[k] k) : Submodule A M :=
  (RingHom.ker ε.toRingHom) • (⊤ : Submodule A M)

/-- The actual fibre M/(ker ε)M, with its inherited k-vector-space structure. -/
abbrev augmentationFibre (ε : A →ₐ[k] k) := M ⧸ augmentationSubmodule (M := M) ε

theorem augmentationFibre_mk_smul (ε : A →ₐ[k] k) (a : A) (x : M) :
    (Submodule.Quotient.mk (a • x) : augmentationFibre (M := M) ε) =
      ε a • Submodule.Quotient.mk x := by
  rw [← Submodule.Quotient.mk_smul]
  apply (Submodule.Quotient.eq _).mpr
  have ha : a - algebraMap k A (ε a) ∈ RingHom.ker ε.toRingHom := by
    change ε (a - algebraMap k A (ε a)) = 0
    simp
  have hm := Submodule.smul_mem_smul ha (show x ∈ (⊤ : Submodule A M) from trivial)
  simpa only [augmentationSubmodule, sub_smul, algebraMap_smul] using hm

/-- A finite A-generating family becomes a k-generating family in the actual augmentation fibre. -/
theorem augmentationFibre_span_eq_top (ε : A →ₐ[k] k) {ι : Type} (v : ι → M)
    (hv : Submodule.span A (Set.range v) = ⊤) :
    Submodule.span k (Set.range (fun i =>
      (Submodule.Quotient.mk (v i) : augmentationFibre (M := M) ε))) = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (augmentationSubmodule (M := M) ε) q
  have hx : x ∈ Submodule.span A (Set.range v) := by rw [hv]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    change (Submodule.Quotient.mk (a • x) : augmentationFibre (M := M) ε) ∈ _
    rw [augmentationFibre_mk_smul]
    exact Submodule.smul_mem _ _ ih

theorem augmentationFibre_finite (ε : A →ₐ[k] k) {ι : Type} [Finite ι] (v : ι → M)
    (hv : Submodule.span A (Set.range v) = ⊤) :
    Module.Finite k (augmentationFibre (M := M) ε) := by
  apply Module.Finite.of_fg_top
  rw [← augmentationFibre_span_eq_top ε v hv]
  exact Submodule.fg_span (Set.finite_range _)

theorem augmentationFibre_finrank_le (ε : A →ₐ[k] k) {ι : Type} [Fintype ι] (v : ι → M)
    (hv : Submodule.span A (Set.range v) = ⊤) :
    Module.finrank k (augmentationFibre (M := M) ε) ≤ Fintype.card ι := by
  exact finrank_le_of_span_eq_top (augmentationFibre_span_eq_top ε v hv)

end AugmentationFibre
end NSP3.TorSpike
