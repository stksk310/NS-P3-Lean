import P3TorSpike.KoszulCoordinates
import P3TorSpike.RegularReductionTop

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NSP3.TorSpike.RegularReduction
open CategoryTheory
open Koszul
variable (k A : Type) [Field k] [CommRing A] [Algebra k A]

def leftZeroEquiv : A ≃ₗ[k] (Fin 0 → A) × A where
  toFun x := (0,x)
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by
    apply Prod.ext
    · funext i; exact Fin.elim0 i
    · rfl
  map_add' x y := by
    apply Prod.ext
    · funext i; exact Fin.elim0 i
    · rfl
  map_smul' r x := by
    apply Prod.ext
    · funext i; exact Fin.elim0 i
    · rfl

def rightZeroEquiv : A ≃ₗ[k] A × (Fin 0 → A) where
  toFun x := (x,0)
  invFun x := x.1
  left_inv _ := rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i; exact Fin.elim0 i
  map_add' x y := by
    apply Prod.ext
    · rfl
    · funext i; exact Fin.elim0 i
  map_smul' r x := by
    apply Prod.ext
    · rfl
    · funext i; exact Fin.elim0 i
@[simp] theorem baseComplex_d (u : Fin 4 → A) (n : ℕ) :
    (baseComplex k A u).d (n+1) n = ModuleCat.ofHom (baseDifferential k A u n) :=
  ChainComplex.of_d (fun n => ModuleCat.of k (baseGraded k A n))
    (fun n => ModuleCat.ofHom (baseDifferential k A u n)) n

def genericConeH1Complex (t : A) (u : Fin 3 → A) : ShortComplex (ModuleCat.{0} k) :=
  coneShortComplex (threeH1Complex k A u) (multiplyH1 k A t u)
    (0 : A →ₗ[k] (Fin 0 → A)) (by rfl)

def genericConeH2Complex (t : A) (u : Fin 3 → A) : ShortComplex (ModuleCat.{0} k) :=
  coneShortComplex (threeH2Complex k A u) (multiplyH2 k A t u)
    (threeD1 k A u) (threeD1_comp_threeD2 k A u)

def genericConeH3Complex (t : A) (u : Fin 3 → A) : ShortComplex (ModuleCat.{0} k) :=
  coneShortComplex (threeH3Complex k A u) (multiplyH3 k A t u)
    (threeD2 k A u) (threeD2_comp_threeD3 k A u)

/-- Binary exterior coordinates identify the actual four-variable short complex with the cone. -/
def baseH1ConeIso (u : Fin 4 → A) :
    (baseComplex k A u).sc' 2 1 0 ≅ genericConeH1Complex k A (u 0) (tailGenerators A u) := by
  refine ShortComplex.isoMk (coordinates2 k A).toModuleIso (coordinates1 k A).toModuleIso
    ((coordinates0 k A).trans (leftZeroEquiv k A)).toModuleIso ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', baseComplex_d]
    change (-threeD1 k A (tailGenerators A u) (coordinates2 k A v).1,
      multiplyPi k A (u 0) (Fin 3) (coordinates2 k A v).1 +
        threeD2 k A (tailGenerators A u) (coordinates2 k A v).2) =
      coordinates1 k A (baseDifferential k A u 1 v)
    exact (coordinates_d2 k A u v).symm
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', baseComplex_d]
    change coneOutgoing (threeH1Complex k A (tailGenerators A u))
      (multiplyH1 k A (u 0) (tailGenerators A u))
      (0 : A →ₗ[k] (Fin 0 → A)) (coordinates1 k A v) =
      leftZeroEquiv k A (coordinates0 k A (baseDifferential k A u 0 v))
    apply Prod.ext
    · funext i; exact Fin.elim0 i
    · change multiply k A (u 0) (coordinates1 k A v).1 +
        threeD1 k A (tailGenerators A u) (coordinates1 k A v).2 =
        coordinates0 k A (baseDifferential k A u 0 v)
      simpa only [multiply_apply] using (coordinates_d1 k A u v).symm

def baseH2ConeIso (u : Fin 4 → A) :
    (baseComplex k A u).sc' 3 2 1 ≅ genericConeH2Complex k A (u 0) (tailGenerators A u) := by
  refine ShortComplex.isoMk (coordinates3 k A).toModuleIso (coordinates2 k A).toModuleIso
    (coordinates1 k A).toModuleIso ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', baseComplex_d]
    change (-threeD2 k A (tailGenerators A u) (coordinates3 k A v).1,
      multiplyPi k A (u 0) (Fin 3) (coordinates3 k A v).1 +
        threeD3 k A (tailGenerators A u) (coordinates3 k A v).2) =
      coordinates2 k A (baseDifferential k A u 2 v)
    exact (coordinates_d3 k A u v).symm
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', baseComplex_d]
    change (-threeD1 k A (tailGenerators A u) (coordinates2 k A v).1,
      multiplyPi k A (u 0) (Fin 3) (coordinates2 k A v).1 +
        threeD2 k A (tailGenerators A u) (coordinates2 k A v).2) =
      coordinates1 k A (baseDifferential k A u 1 v)
    exact (coordinates_d2 k A u v).symm

def baseH3ConeIso (u : Fin 4 → A) :
    (baseComplex k A u).sc' 4 3 2 ≅ genericConeH3Complex k A (u 0) (tailGenerators A u) := by
  refine ShortComplex.isoMk ((coordinates4 k A).trans (rightZeroEquiv k A)).toModuleIso
    (coordinates3 k A).toModuleIso (coordinates2 k A).toModuleIso ?_ ?_
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', baseComplex_d]
    change coneIncoming (threeH3Complex k A (tailGenerators A u))
      (multiplyH3 k A (u 0) (tailGenerators A u))
      (rightZeroEquiv k A (coordinates4 k A v)) =
      coordinates3 k A (baseDifferential k A u 3 v)
    apply Prod.ext
    · exact (congrArg Prod.fst (coordinates_d4 k A u v)).symm
    · change multiply k A (u 0) (coordinates4 k A v) + 0 =
        (coordinates3 k A (baseDifferential k A u 3 v)).2
      simpa only [multiply_apply,add_zero] using
        (congrArg Prod.snd (coordinates_d4 k A u v)).symm
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', baseComplex_d]
    change (-threeD2 k A (tailGenerators A u) (coordinates3 k A v).1,
      multiplyPi k A (u 0) (Fin 3) (coordinates3 k A v).1 +
        threeD3 k A (tailGenerators A u) (coordinates3 k A v).2) =
      coordinates2 k A (baseDifferential k A u 2 v)
    exact (coordinates_d3 k A u v).symm

/-- Direct actual first Koszul homology comparison with the quotient by a regular first variable. -/
def baseH1ReductionEquiv (u : Fin 4 → A) (ht : Function.Injective (multiply k A (u 0))) :
    (baseComplex k A u).homology 1 ≃ₗ[k]
      (threeH1Complex k (QuotientRing A (u 0))
        (fun i => quotientAlg k A (u 0) (tailGenerators A u i))).homology :=
  ((baseComplex k A u).homologyIsoSc' 2 1 0 (by simp) (by simp)).toLinearEquiv.trans
    ((ShortComplex.homologyMapIso (baseH1ConeIso k A u)).toLinearEquiv.trans
      (regularH1Equiv k A (u 0) (tailGenerators A u) ht))

def baseH2ReductionEquiv (u : Fin 4 → A) (ht : Function.Injective (multiply k A (u 0))) :
    (baseComplex k A u).homology 2 ≃ₗ[k]
      (threeH2Complex k (QuotientRing A (u 0))
        (fun i => quotientAlg k A (u 0) (tailGenerators A u i))).homology :=
  ((baseComplex k A u).homologyIsoSc' 3 2 1 (by simp) (by simp)).toLinearEquiv.trans
    ((ShortComplex.homologyMapIso (baseH2ConeIso k A u)).toLinearEquiv.trans
      (regularH2Equiv k A (u 0) (tailGenerators A u) ht))

def baseH3ReductionEquiv (u : Fin 4 → A) (ht : Function.Injective (multiply k A (u 0))) :
    (baseComplex k A u).homology 3 ≃ₗ[k]
      LinearMap.ker (threeD3 k (QuotientRing A (u 0))
        (fun i => quotientAlg k A (u 0) (tailGenerators A u i))) :=
  ((baseComplex k A u).homologyIsoSc' 4 3 2 (by simp) (by simp)).toLinearEquiv.trans
    ((ShortComplex.homologyMapIso (baseH3ConeIso k A u)).toLinearEquiv.trans
      ((regularH3Equiv k A (u 0) (tailGenerators A u) ht).trans
        (threeH3EquivKer k (QuotientRing A (u 0)) _)))



/-- Regularity of the first coefficient detects the sole top exterior coordinate. -/
theorem baseTop_injective (u : Fin 4 → A) (ht : Function.Injective (multiply k A (u 0))) :
    Function.Injective (baseDifferential k A u 3) := by
  intro v w h
  apply (coordinates4 k A).injective
  apply ht
  change u 0 * coordinates4 k A v = u 0 * coordinates4 k A w
  have h₂ := congrArg (fun x : baseGraded k A 3 => (coordinates3 k A x).2) h
  simpa only [coordinates_d4] using h₂

theorem baseExactAt_four (u : Fin 4 → A) (ht : Function.Injective (multiply k A (u 0))) :
    (baseComplex k A u).ExactAt 4 := by
  rw [HomologicalComplex.exactAt_iff' _ 5 4 3 (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro v hv
  have hv' : baseDifferential k A u 3 v = 0 := by
    have h : (baseComplex k A u).d 4 3 v = 0 := hv
    rw [baseComplex_d k A u 3] at h
    exact h
  have he : v = 0 := baseTop_injective k A u ht (by simpa only [map_zero] using hv')
  exact ⟨0,by simpa [he]⟩

theorem baseExactAt_ge5 (u : Fin 4 → A) (n : ℕ) (hn : 5 ≤ n) :
    (baseComplex k A u).ExactAt n := by
  letI : Subsingleton ((baseComplex k A u).X n) := by
    change Subsingleton (baseGraded k A n)
    refine ⟨fun v w => ?_⟩
    apply Subtype.ext
    funext i
    have hi : degree i ≠ n := by have hd := degree_le_four i; omega
    rw [v.property i hi,w.property i hi]
  exact ShortComplex.exact_of_isZero_X₂ _ (ModuleCat.isZero_of_subsingleton ((baseComplex k A u).X n))

theorem baseHomology_isZero_ge4 (u : Fin 4 → A)
    (ht : Function.Injective (multiply k A (u 0))) (n : ℕ) (hn : 4 ≤ n) :
    CategoryTheory.Limits.IsZero ((baseComplex k A u).homology n) := by
  by_cases he : n = 4
  · subst n
    exact (baseExactAt_four k A u ht).isZero_homology
  · exact (baseExactAt_ge5 k A u n (by omega)).isZero_homology
end NSP3.TorSpike.RegularReduction
