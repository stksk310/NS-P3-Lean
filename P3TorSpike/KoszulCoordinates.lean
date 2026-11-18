import P3TorSpike.KoszulBaseChange
import P3TorSpike.ReductionComplex

noncomputable section
namespace NSP3.TorSpike.Koszul
variable (k A : Type) [Field k] [CommRing A] [Algebra k A]

def coordinates0 : baseGraded k A 0 ≃ₗ[k] A where
  toFun v := v.val 0
  invFun x := ⟨![x,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0], by
    intro i hi; fin_cases i <;> simp_all [degree]⟩
  left_inv v := by
    apply Subtype.ext; funext i
    fin_cases i <;> first | rfl | exact (v.property _ (by decide)).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinates1 : baseGraded k A 1 ≃ₗ[k] A × (Fin 3 → A) where
  toFun v := (v.val 1, ![v.val 2,v.val 4,v.val 8])
  invFun x := ⟨![0,x.1,x.2 0,0,x.2 1,0,0,0,x.2 2,0,0,0,0,0,0,0], by
    intro i hi; fin_cases i <;> simp_all [degree]⟩
  left_inv v := by
    apply Subtype.ext; funext i
    fin_cases i <;> first | rfl | exact (v.property _ (by decide)).symm
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> rfl
  map_add' v w := by
    apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> rfl
  map_smul' r v := by
    apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> rfl

def coordinates2 : baseGraded k A 2 ≃ₗ[k] (Fin 3 → A) × (Fin 3 → A) where
  toFun v := (![v.val 3,v.val 5,v.val 9], ![v.val 6,v.val 10,v.val 12])
  invFun x := ⟨![0,0,0,x.1 0,0,x.1 1,x.2 0,0,0,x.1 2,x.2 1,0,x.2 2,0,0,0], by
    intro i hi; fin_cases i <;> simp_all [degree]⟩
  left_inv v := by
    apply Subtype.ext; funext i
    fin_cases i <;> first | rfl | exact (v.property _ (by decide)).symm
  right_inv x := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_add' v w := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl
  map_smul' r v := by
    apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

def coordinates3 : baseGraded k A 3 ≃ₗ[k] (Fin 3 → A) × A where
  toFun v := (![v.val 7,v.val 11,v.val 13], v.val 14)
  invFun x := ⟨![0,0,0,0,0,0,0,x.1 0,0,0,0,x.1 1,0,x.1 2,x.2,0], by
    intro i hi; fin_cases i <;> simp_all [degree]⟩
  left_inv v := by
    apply Subtype.ext; funext i
    fin_cases i <;> first | rfl | exact (v.property _ (by decide)).symm
  right_inv x := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  map_add' v w := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl
  map_smul' r v := by
    apply Prod.ext
    · funext i; fin_cases i <;> rfl
    · rfl

def coordinates4 : baseGraded k A 4 ≃ₗ[k] A where
  toFun v := v.val 15
  invFun x := ⟨![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,x], by
    intro i hi; fin_cases i <;> simp_all [degree]⟩
  left_inv v := by
    apply Subtype.ext; funext i
    fin_cases i <;> first | rfl | exact (v.property _ (by decide)).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def tailGenerators (u : Fin 4 → A) : Fin 3 → A := ![u 1,u 2,u 3]

theorem coordinates_d1 (u : Fin 4 → A) (v : baseGraded k A 1) :
    coordinates0 k A (baseDifferential k A u 0 v) =
      u 0 * (coordinates1 k A v).1 + threeD1 k A (tailGenerators A u) (coordinates1 k A v).2 := by
  change u 0 * v.val 1 + u 1 * v.val 2 + u 2 * v.val 4 + u 3 * v.val 8 =
    u 0 * v.val 1 + (u 1 * v.val 2 + u 2 * v.val 4 + u 3 * v.val 8)
  ring

theorem coordinates_d2 (u : Fin 4 → A) (v : baseGraded k A 2) :
    coordinates1 k A (baseDifferential k A u 1 v) =
      (-(threeD1 k A (tailGenerators A u) (coordinates2 k A v).1),
       u 0 • (coordinates2 k A v).1 + threeD2 k A (tailGenerators A u) (coordinates2 k A v).2) := by
  apply Prod.ext
  · change (-u 1) * v.val 3 - u 2 * v.val 5 - u 3 * v.val 9 =
      -(u 1 * v.val 3 + u 2 * v.val 5 + u 3 * v.val 9)
    ring
  · funext i
    fin_cases i
    · change u 0 * v.val 3 - u 2 * v.val 6 - u 3 * v.val 10 =
        u 0 * v.val 3 + (-(u 2 * v.val 6) - u 3 * v.val 10)
      ring
    · change u 0 * v.val 5 + u 1 * v.val 6 - u 3 * v.val 12 =
        u 0 * v.val 5 + (u 1 * v.val 6 - u 3 * v.val 12)
      ring
    · change u 0 * v.val 9 + u 1 * v.val 10 + u 2 * v.val 12 =
        u 0 * v.val 9 + (u 1 * v.val 10 + u 2 * v.val 12)
      ring

theorem coordinates_d3 (u : Fin 4 → A) (v : baseGraded k A 3) :
    coordinates2 k A (baseDifferential k A u 2 v) =
      (-(threeD2 k A (tailGenerators A u) (coordinates3 k A v).1),
       u 0 • (coordinates3 k A v).1 + threeD3 k A (tailGenerators A u) (coordinates3 k A v).2) := by
  apply Prod.ext
  · funext i
    fin_cases i
    · change u 2 * v.val 7 + u 3 * v.val 11 = -(-(u 2 * v.val 7) - u 3 * v.val 11)
      ring
    · change (-u 1) * v.val 7 + u 3 * v.val 13 = -(u 1 * v.val 7 - u 3 * v.val 13)
      ring
    · change (-u 1) * v.val 11 - u 2 * v.val 13 = -(u 1 * v.val 11 + u 2 * v.val 13)
      ring
  · funext i
    fin_cases i
    · rfl
    · change u 0 * v.val 11 - u 2 * v.val 14 = u 0 * v.val 11 + -(u 2 * v.val 14)
      ring
    · rfl

theorem coordinates_d4 (u : Fin 4 → A) (v : baseGraded k A 4) :
    coordinates3 k A (baseDifferential k A u 3 v) =
      (-(threeD3 k A (tailGenerators A u) (coordinates4 k A v)),
       u 0 * coordinates4 k A v) := by
  apply Prod.ext
  · funext i
    fin_cases i
    · change (-u 3) * v.val 15 = -(u 3 * v.val 15)
      ring
    · change u 2 * v.val 15 = -(-(u 2 * v.val 15))
      ring
    · change (-u 1) * v.val 15 = -(u 1 * v.val 15)
      ring
  · rfl

end NSP3.TorSpike.Koszul
