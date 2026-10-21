import NSP3.SymbolicBWExceptional
import NSP3.SymbolicBWBulk

namespace NSP3

/-- The original residual BF obligation, without new exclusions or g bounds. -/
theorem fullSupport_smallwidth_remaining_BF_lower
    (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S)
    (ht : 4 ≤ pair23Count S.D)
    (hr : pair12Count S.D ≤ 17)
    (hvar : pair12Count S.D+6 < 2*(pair13Count S.D+pair23Count S.D))
    (hstrip : (pair23Count S.D=4 ∧ pair13Count S.D≤8) ∨
      (pair23Count S.D=5 ∧ pair13Count S.D≤6) ∨
      (pair23Count S.D=6 ∧ pair13Count S.D=6))
    (hne444 : ¬ (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4)) :
    fullTarget S ≤ fullSupportSymbolicBF S g := by
  have _ := ht
  by_cases hq : (pair12Count S.D=6 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=7 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=6 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=6 ∧ pair13Count S.D=6 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=5)
  · exact le_trans (fullSupport_smallwidth_six_BW_lower S hg hf ho hq)
      (fullSupportSymbolicBW_le_BF S g)
  by_cases h544 : pair12Count S.D=5 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4
  · have h := fullSupport_q544_BF_sharp_lower S hg hf ho h544.1 h544.2.1 h544.2.2
    have he : fullTarget S=57 := by rw [fullTarget_eq_square,h544.1,h544.2.1,h544.2.2]; decide
    rw [he]
    exact h
  · apply le_trans (fullSupport_smallwidth_core_bulk_BW_sharp S hg hf ho ?_ ?_)
      (fullSupportSymbolicBW_le_BF S g)
    · rcases hstrip with h | h | h <;> omega
    · have hs := ho.1
      have hr' := ho.2
      omega

theorem fullSupport_tGE4_ordered_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : 4 ≤ pair23Count S.D) : fullTarget S ≤ S.m := by
  rcases fullSupport_tGE4_residual_cover S hg hf ho ht with h | h
  · exact h
  · exact le_trans (fullSupport_smallwidth_remaining_BF_lower S hg hf ho ht
      h.1 h.2.1 h.2.2.1 h.2.2.2) (fullSupport_symbolic_BF_lower S hg hf ho)

/-- All ordered full-support cases, but NOT coordinate transport or semigroup P3. -/
theorem fullSupport_ordered_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    fullTarget S ≤ S.m := by
  by_cases ht4 : 4 ≤ pair23Count S.D
  · exact fullSupport_tGE4_ordered_symbolic_sharp S hg hf ho ht4
  have hc : pair23Count S.D=0 ∨ pair23Count S.D=1 ∨
      pair23Count S.D=2 ∨ pair23Count S.D=3 := by omega
  rcases hc with ht | ht | ht | ht
  · exact le_of_lt (fullSupport_t0_strict S hg hf ho ht)
  · exact fullSupport_t1_ordered_symbolic_sharp S hg hf ho ht
  · exact fullSupport_t2_ordered_symbolic_sharp S hg hf ho ht
  · exact fullSupport_t3_ordered_symbolic_sharp S hg hf ho ht

end NSP3
