import P3TorSpike.KoszulRelationsLift
import P3TorSpike.BinomialTuple

noncomputable section
namespace NSP3.TorSpike.Koszul
open MvPolynomial
variable (k : Type) [Field k] (m a b c : ℕ)

/-- A tuple of actual relations, placed in exterior degree one. -/
def relationTuple (f : Fin 4 → relationKernel k m a b c) : graded k 1 :=
  ⟨![0, (f 0).val, (f 1).val, 0, (f 2).val, 0, 0, 0, (f 3).val,
      0, 0, 0, 0, 0, 0, 0], by
    intro i hi
    fin_cases i <;> simp_all [degree]⟩

theorem relationTuple_project (f : Fin 4 → relationKernel k m a b c) :
    relationProject k m a b c 1 (relationTuple k m a b c f) = 0 := by
  have hf (i : Fin 4) : polynomialMap k m a b c (f i).val = 0 := (f i).property
  apply Subtype.ext
  funext i
  change polynomialMap k m a b c ((relationTuple k m a b c f).val i) = 0
  fin_cases i <;> simp [relationTuple, hf]

theorem relationTuple_differential (f : Fin 4 → relationKernel k m a b c) :
    (gradedDifferential k 0 (relationTuple k m a b c f)).val 0 =
      ∑ i, (X i : PolynomialRing k) * (f i).val := by
  change differential (relationTuple k m a b c f).val 0 = _
  simp [differential, relationTuple, Fin.sum_univ_succ, add_assoc]

theorem differential_mem_augmentation_of_project_zero (p : graded k 1)
    (hp : relationProject k m a b c 1 p = 0) (x : relationKernel k m a b c)
    (hx : x.val = (gradedDifferential k 0 p).val 0) :
    x ∈ augmentationSubmodule (M := relationKernel k m a b c) (polynomialAugmentation k) := by
  have hp' (i : Fin 16) : polynomialMap k m a b c (p.val i) = 0 :=
    congrArg (fun v => v.val i) hp
  let f : Fin 4 → relationKernel k m a b c :=
    ![⟨p.val 1, hp' 1⟩, ⟨p.val 2, hp' 2⟩, ⟨p.val 4, hp' 4⟩, ⟨p.val 8, hp' 8⟩]
  apply (relationKernel_augmentationSubmodule_tuple k m a b c x).mpr
  refine ⟨f, ?_⟩
  rw [hx]
  change ∑ i, (X i : PolynomialRing k) * (f i).val = differential p.val 0
  simp [f, Fin.sum_univ_succ, differential, add_assoc]

/-- The cycle-to-relation map with the actual augmentation quotient as codomain. -/
def relationCycleClass : relationCycles k m a b c →ₗ[k] relationConormal k m a b c :=
  (((augmentationSubmodule (M := relationKernel k m a b c) (polynomialAugmentation k)).mkQ).restrictScalars k).comp (relationCycleKernel k m a b c)

theorem graded_zero_ext {v w : graded k 0} (h : v.val 0 = w.val 0) : v = w := by
  apply Subtype.ext
  funext i
  fin_cases i
  · exact h
  all_goals exact (v.2 _ (by decide)).trans (w.2 _ (by decide)).symm

end NSP3.TorSpike.Koszul
