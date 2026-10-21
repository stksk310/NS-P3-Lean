import NSP3.PlaneDefects

namespace NSP3

#check monotone_suffix_sum_lower
#check antitone_prefix_sum_lower
#check exactBlock_of_defect_sum
#check pair12ExactBlock_of_defect_bound
#check pair13ExactBlock_of_defect_bound
#check pair23ExactBlock_of_defect_bound
#check pair12Extra_card_ge_totalDefect
#check pair13Extra_card_ge_totalDefect
#check pair23Extra_card_ge_totalDefect
#check pair12ExactBlock
#check pair13ExactBlock
#check pair23ExactBlock

example : ∃ B : ExactDefectBlock 1 (fun _ => 0) (fun _ => 0) 1, B.length ≥ 1 := by
  have h := exactBlock_of_defect_sum (q := 1) (e := 0)
    (α := fun _ => 0) (γ := fun _ => 0)
    (by intro a b hab; rfl) (by intro a b hab; rfl) (by simp) (by omega)
  exact ⟨h, h.length_lower⟩

/-- A genuinely deformed Ferrers profile still contains the predicted exact block. -/
example : ∃ B : ExactDefectBlock 5 (![0, 0, 0, 1, 1] : Fin 5 → ℕ)
    (![1, 0, 0, 0, 0] : Fin 5 → ℕ) 2, B.length ≥ 2 := by
  let α : Fin 5 → ℕ := ![0, 0, 0, 1, 1]
  let γ : Fin 5 → ℕ := ![1, 0, 0, 0, 0]
  have hα : Monotone α := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [α]
  have hγ : Antitone γ := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [γ]
  have hsum : (∑ i : Fin 5, (α i + γ i)) ≤ 3 := by native_decide
  have h := exactBlock_of_defect_sum (q := 5) (e := 3) hα hγ hsum (by omega)
  exact ⟨h, h.length_lower⟩

end NSP3
