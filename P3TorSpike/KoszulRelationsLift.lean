import P3TorSpike.KoszulAugmentation
import P3TorSpike.KoszulBaseChange
import P3TorSpike.BinomialSection

noncomputable section
namespace NSP3.TorSpike.Koszul
open MvPolynomial
variable (k : Type) [Field k] (m a b c : ℕ)

def relationValues : Fin 4 → SemigroupRing k m a b c :=
  fun i => monomial k (generator m a b c i)

/-- The existing monomial normal section lifts every coordinate k-linearly. -/
def relationLift (n : ℕ) :
    baseGraded k (SemigroupRing k m a b c) n →ₗ[k] graded k n where
  toFun v := ⟨fun i => normalSection k m a b c (v.1 i), by
    intro i hi
    change normalSection k m a b c (v.1 i) = 0
    rw [v.2 i hi, map_zero]⟩
  map_add' v w := by
    apply Subtype.ext
    funext i
    exact map_add (normalSection k m a b c) _ _
  map_smul' r v := by
    apply Subtype.ext
    funext i
    exact map_smul (normalSection k m a b c) _ _

/-- The true polynomial quotient map in each exterior degree. -/
def relationProject (n : ℕ) :
    graded k n →ₗ[k] baseGraded k (SemigroupRing k m a b c) n where
  toFun v := ⟨fun i => polynomialMap k m a b c (v.1 i), by
    intro i hi
    change polynomialMap k m a b c (v.1 i) = 0
    rw [v.2 i hi, map_zero]⟩
  map_add' v w := by
    apply Subtype.ext
    funext i
    exact map_add (polynomialMap k m a b c) _ _
  map_smul' r v := by
    apply Subtype.ext
    funext i
    exact map_smul (polynomialMap k m a b c) _ _

@[simp] theorem relationProject_val (n : ℕ) (v : graded k n) (i : Fin 16) :
    (relationProject k m a b c n v).val i = polynomialMap k m a b c (v.val i) := rfl

@[simp] theorem relationProject_lift (n : ℕ)
    (v : baseGraded k (SemigroupRing k m a b c) n) :
    relationProject k m a b c n (relationLift k m a b c n v) = v := by
  apply Subtype.ext
  funext i
  exact polynomialMap_normalSection k m a b c _

theorem relationProject_differential (n : ℕ) (v : graded k (n+1)) :
    relationProject k m a b c n (gradedDifferential k n v) =
      baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) n
        (relationProject k m a b c (n+1) v) := by
  apply Subtype.ext
  funext i
  change polynomialMap k m a b c (differential v.1 i) =
    baseCubeD (SemigroupRing k m a b c) (relationValues k m a b c)
      (relationProject k m a b c (n+1) v).1 i
  fin_cases i <;>
    simp [differential, baseCubeD, relationValues, relationProject_val]

abbrev relationCycles :=
  LinearMap.ker (baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) 0)

def relationCyclePolynomial : relationCycles k m a b c →ₗ[k] PolynomialRing k :=
  (((LinearMap.proj (0 : Fin 16)).comp ((graded k 0).subtype.restrictScalars k)).comp
    ((gradedDifferential k 0).restrictScalars k)).comp
      ((relationLift k m a b c 1).comp (relationCycles k m a b c).subtype)

theorem relationCyclePolynomial_mem (v : relationCycles k m a b c) :
    relationCyclePolynomial k m a b c v ∈ relationKernel k m a b c := by
  have hc := relationProject_differential k m a b c 0 (relationLift k m a b c 1 v.1)
  rw [relationProject_lift] at hc
  have hv : baseDifferential k (SemigroupRing k m a b c) (relationValues k m a b c) 0 v.1 = 0 :=
    v.2
  rw [hv] at hc
  exact congrArg (fun w => w.val 0) hc

/-- The actual cycle-to-relation map, before quotienting by augmentation multiples. -/
def relationCycleKernel : relationCycles k m a b c →ₗ[k] relationKernel k m a b c :=
  (relationCyclePolynomial k m a b c).codRestrict
    ((relationKernel k m a b c).restrictScalars k) (relationCyclePolynomial_mem k m a b c)

end NSP3.TorSpike.Koszul
