import P3TorSpike.KoszulAugmentation

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace NSP3.TorSpike.Koszul
open CategoryTheory
variable {k : Type} [Field k]

@[simp] theorem complex_d (k : Type) [Field k] (n : ℕ) :
    (complex k).d (n+1) n = ModuleCat.ofHom (gradedDifferential k n) := by
  exact ChainComplex.of_d (fun n => ModuleCat.of (PolynomialRing k) (graded k n))
    (fun n => ModuleCat.ofHom (gradedDifferential k n)) n

@[simp] theorem complex_d_succ (k : Type) [Field k] (n : ℕ) :
    (complex k).d (n+2) (n+1) = ModuleCat.ofHom (gradedDifferential k (n+1)) :=
  complex_d k (n+1)

theorem complex_exactAt_succ (k : Type) [Field k] (n : ℕ) :
    (complex k).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    complex_d, complex_d_succ]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro v hv
  change gradedDifferential k n v = 0 at hv
  exact exact_positive n v hv

def augmentationChainMap (k : Type) [Field k] :
    complex k ⟶ (ChainComplex.single₀ (ModuleCat (PolynomialRing k))).obj (residueModule k) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨augmentation k, by
    rw [complex_d]
    exact augmentation_differential k⟩

/-- The genuine finite free polynomial Koszul resolution of the actual residue module.
Exactness is proved by the explicit polynomial-division contraction, over every field. -/
def resolution (k : Type) [Field k] : ProjectiveResolution (residueModule k) where
  complex := complex k
  π := augmentationChainMap k
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso
          (S₂ := ShortComplex.mk (ModuleCat.ofHom (gradedDifferential k 0))
            (augmentation k) (augmentation_differential k)) ?_).2 ?_
        · exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
            (by
              change 𝟙 _ ≫ ModuleCat.ofHom (gradedDifferential k 0) =
                (complex k).d 1 0 ≫ 𝟙 _
              rw [complex_d]
              simp only [Category.id_comp, Category.comp_id])
            (by
              change 𝟙 _ ≫ augmentation k = (augmentationChainMap k).f 0 ≫ 𝟙 _
              simp only [augmentationChainMap, ChainComplex.toSingle₀Equiv_symm_apply_f_zero,
                Category.id_comp, Category.comp_id])
        · refine ⟨?_, augmentation_epi k⟩
          apply (ShortComplex.moduleCat_exact_iff _).mpr
          intro v hv
          exact exact_zero v hv
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt_succ k n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end NSP3.TorSpike.Koszul
