import P3TorSpike.KoszulRelationsQuotient
import P3TorSpike.KoszulResolution

noncomputable section
namespace NSP3.TorSpike.Koszul
open MvPolynomial
variable (k : Type) [Field k] (m a b c : ℕ)

theorem relationCycleClass_eq_of_lift (v : relationCycles k m a b c) (p : graded k 1)
    (hp : relationProject k m a b c 1 p = v.val) (q : relationKernel k m a b c)
    (hq : q.val = (gradedDifferential k 0 p).val 0) :
    relationCycleClass k m a b c v = (Submodule.Quotient.mk q : relationConormal k m a b c) := by
  change (Submodule.Quotient.mk (relationCycleKernel k m a b c v) : relationConormal k m a b c) = _
  apply (Submodule.Quotient.eq _).mpr
  apply differential_mem_augmentation_of_project_zero k m a b c
    (relationLift k m a b c 1 v.val - p)
  · rw [map_sub, relationProject_lift, hp, sub_self]
  · change (gradedDifferential k 0 (relationLift k m a b c 1 v.val)).val 0 - q.val = _
    rw [map_sub]
    change (gradedDifferential k 0 (relationLift k m a b c 1 v.val)).val 0 - q.val =
      (gradedDifferential k 0 (relationLift k m a b c 1 v.val)).val 0 -
        (gradedDifferential k 0 p).val 0
    rw [hq]

def relationBoundary : baseGraded k (SemigroupRing k m a b c) 2 →ₗ[k] relationCycles k m a b c :=
  (baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) 1).codRestrict _
    (fun w => by
      change baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) 0
        (baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) 1 w) = 0
      exact LinearMap.congr_fun
        (baseDifferential_squared k (SemigroupRing k m a b c) (relationValues k m a b c) 0) w)

theorem relationCycleClass_boundary (w : baseGraded k (SemigroupRing k m a b c) 2) :
    relationCycleClass k m a b c (relationBoundary k m a b c w) = 0 := by
  have hp : relationProject k m a b c 1
      (gradedDifferential k 1 (relationLift k m a b c 2 w)) =
        (relationBoundary k m a b c w).val := by
    rw [relationProject_differential, relationProject_lift]
    rfl
  have hq : (0 : relationKernel k m a b c).val =
      (gradedDifferential k 0 (gradedDifferential k 1 (relationLift k m a b c 2 w))).val 0 := by
    change 0 = differential (differential (relationLift k m a b c 2 w).val) 0
    rw [differential_squared]
    rfl
  simpa using relationCycleClass_eq_of_lift k m a b c (relationBoundary k m a b c w)
    _ hp 0 hq

theorem relationCycleClass_exact (v : relationCycles k m a b c)
    (hv : relationCycleClass k m a b c v = 0) :
    ∃ w, relationBoundary k m a b c w = v := by
  have hq : relationCycleKernel k m a b c v ∈
      augmentationSubmodule (M := relationKernel k m a b c) (polynomialAugmentation k) :=
    (Submodule.Quotient.mk_eq_zero _).mp hv
  obtain ⟨f, hf⟩ := (relationKernel_augmentationSubmodule_tuple k m a b c _).mp hq
  let p : graded k 1 := relationLift k m a b c 1 v.val - relationTuple k m a b c f
  have hp : gradedDifferential k 0 p = 0 := by
    apply graded_zero_ext
    change (gradedDifferential k 0 p).val 0 = 0
    dsimp [p]
    rw [map_sub]
    change (gradedDifferential k 0 (relationLift k m a b c 1 v.val)).val 0 -
      (gradedDifferential k 0 (relationTuple k m a b c f)).val 0 = 0
    rw [relationTuple_differential, hf]
    exact sub_self _
  obtain ⟨z, hz⟩ := exact_positive 0 p hp
  refine ⟨relationProject k m a b c 2 z, ?_⟩
  apply Subtype.ext
  change baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) 1
    (relationProject k m a b c 2 z) = v.val
  rw [← relationProject_differential, hz]
  dsimp [p]
  rw [map_sub, relationProject_lift, relationTuple_project, sub_zero]

def relationDegreeZero (x : relationKernel k m a b c) : graded k 0 :=
  ⟨![x.val, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], by
    intro i hi
    fin_cases i <;> simp_all [degree]⟩

@[simp] theorem relationDegreeZero_val (x : relationKernel k m a b c) :
    (relationDegreeZero k m a b c x).val 0 = x.val := by
  rfl

theorem relationDegreeZero_project (x : relationKernel k m a b c) :
    relationProject k m a b c 0 (relationDegreeZero k m a b c x) = 0 := by
  have hx : polynomialMap k m a b c x.val = 0 := x.property
  apply Subtype.ext
  funext i
  change polynomialMap k m a b c ((relationDegreeZero k m a b c x).val i) = 0
  fin_cases i <;> simp [relationDegreeZero, hx]

theorem relationCycleClass_surjective (h : MinimalFourGeneratorClass m a b c) :
    Function.Surjective (relationCycleClass k m a b c) := by
  intro q
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective
    (augmentationSubmodule (M := relationKernel k m a b c) (polynomialAugmentation k)) q
  have hx : augmentation k (relationDegreeZero k m a b c x) = 0 := by
    change constantCoeff ((relationDegreeZero k m a b c x).val 0) = 0
    rw [relationDegreeZero_val]
    exact relationKernel_constantCoeff_zero k m a b c h x
  obtain ⟨p, hp⟩ := exact_zero (relationDegreeZero k m a b c x) hx
  have hc : baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) 0
      (relationProject k m a b c 1 p) = 0 := by
    rw [← relationProject_differential, hp, relationDegreeZero_project]
  let v : relationCycles k m a b c := ⟨relationProject k m a b c 1 p, hc⟩
  refine ⟨v, ?_⟩
  apply relationCycleClass_eq_of_lift k m a b c v p rfl x
  rw [hp, relationDegreeZero_val]

end NSP3.TorSpike.Koszul
