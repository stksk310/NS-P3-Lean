import P3TorSpike.KoszulRelationsExact
import P3TorSpike.SemigroupTorKoszul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace NSP3.TorSpike.Koszul
open CategoryTheory
variable (k : Type) [Field k] (m a b c : ℕ)

local instance relationCyclesHasQuotient :
    HasQuotient (↥(relationCycles k m a b c)) (Submodule k (relationCycles k m a b c)) :=
  @Submodule.hasQuotient k (↥(relationCycles k m a b c)) inferInstance inferInstance inferInstance

theorem relationCycleClass_range_boundary :
    LinearMap.range (relationBoundary k m a b c) =
      LinearMap.ker (relationCycleClass k m a b c) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact relationCycleClass_boundary k m a b c w
  · exact relationCycleClass_exact k m a b c v

/-- The actual first Koszul cycle quotient is the actual relation conormal. -/
def relationQuotientEquiv (h : MinimalFourGeneratorClass m a b c) :
    (↥(relationCycles k m a b c) ⧸ LinearMap.range (relationBoundary k m a b c)) ≃ₗ[k]
      relationConormal k m a b c :=
  (Submodule.quotEquivOfEq _ _ (relationCycleClass_range_boundary k m a b c)).trans
    ((relationCycleClass k m a b c).quotKerEquivOfSurjective
      (relationCycleClass_surjective k m a b c h))

def relationShortComplex : ShortComplex (ModuleCat k) :=
  ShortComplex.moduleCatMk
    (baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) 1)
    (baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) 0)
    (baseDifferential_squared k (SemigroupRing k m a b c) (relationValues k m a b c) 0)

def relationShortComplexHomologyIso (h : MinimalFourGeneratorClass m a b c) :
    (relationShortComplex k m a b c).homology ≅ ModuleCat.of k (relationConormal k m a b c) :=
  (relationShortComplex k m a b c).moduleCatHomologyIso ≪≫
    (relationQuotientEquiv k m a b c h).toModuleIso

@[simp] theorem relationComplex_d (n : ℕ) :
    (semigroupKoszulComplex k m a b c).d (n+1) n = ModuleCat.ofHom
      (baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) n) := by
  exact ChainComplex.of_d (fun n => ModuleCat.of k (baseGraded k (SemigroupRing k m a b c) n))
    (fun n => ModuleCat.ofHom
      (baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) n)) n

def relationShortComplexIso :
    (semigroupKoszulComplex k m a b c).sc' 2 1 0 ≅ relationShortComplex k m a b c :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change 𝟙 _ ≫ ModuleCat.ofHom
        (baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) 1) =
          (semigroupKoszulComplex k m a b c).d 2 1 ≫ 𝟙 _
      rw [relationComplex_d]
      simp)
    (by
      change 𝟙 _ ≫ ModuleCat.ofHom
        (baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) 0) =
          (semigroupKoszulComplex k m a b c).d 1 0 ≫ 𝟙 _
      rw [relationComplex_d]
      simp)

/-- The categorical first homology of the actual semigroup Koszul complex is I/mI. -/
def semigroupKoszulH1IsoConormal (h : MinimalFourGeneratorClass m a b c) :
    (semigroupKoszulComplex k m a b c).homology 1 ≅
      ModuleCat.of k (relationConormal k m a b c) :=
  (semigroupKoszulComplex k m a b c).homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (relationShortComplexIso k m a b c) ≪≫
      relationShortComplexHomologyIso k m a b c h

/-- The actual first semigroup Koszul homology is the actual conormal module. -/
def semigroupKoszulH1EquivConormal (h : MinimalFourGeneratorClass m a b c) :
    (semigroupKoszulComplex k m a b c).homology 1 ≃ₗ[k] relationConormal k m a b c :=
  (semigroupKoszulH1IsoConormal k m a b c h).toLinearEquiv

/-- Genuine categorical Tor_1 over P, restricted to k, is the actual conormal module. -/
def torOneConormalFieldIso (h : MinimalFourGeneratorClass m a b c) :
    (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
      (torModule k m a b c 1) ≅ ModuleCat.of k (relationConormal k m a b c) :=
  torKoszulFieldIso k m a b c 1 ≪≫ semigroupKoszulH1IsoConormal k m a b c h

end NSP3.TorSpike.Koszul
