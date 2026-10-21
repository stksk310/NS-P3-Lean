import NSP3.SymbolicT1Sharp
import NSP3.LargeTCofinal
import NSP3.SymbolicTGE4Arithmetic

namespace NSP3

theorem fullSupport_symbolic_H_capacity_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    pair12Count S.D-1 ≤ (fullSupportSymbolicH S g).card := by
  have hc := pair12_terminal_return_capacity_ordered S hg hf ho
  have hp := positive_triple_product_sum_lower g.x g.y g.z hf.1 hf.2.1 hf.2.2
  have hb := symbolic_H_positive_box_lower S hf
  omega

theorem fullSupport_symbolic_BW_capacity_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hr : 1 ≤ pair12Count S.D) :
    4*pair12Count S.D+3+Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+Nat.choose (pair23Count S.D) 2 ≤
        fullSupportSymbolicBW S g := by
  have hh := fullSupport_symbolic_H_capacity_lower S hg hf ho
  have hx := le_max_left (pair12Count S.D) g.x
  have hy := le_max_left (pair12Count S.D) g.y
  have hz := le_max_left (pair12Count S.D) g.z
  have h12 : 1 ≤ ferrersPlaneDefect (pair12Count S.D) g.x g.y := le_max_left _ _
  have h13 : 1 ≤ ferrersPlaneDefect (pair13Count S.D) g.x g.z := le_max_left _ _
  have h23 : 1 ≤ ferrersPlaneDefect (pair23Count S.D) g.y g.z := le_max_left _ _
  unfold fullSupportSymbolicBW
  omega

theorem fullSupport_tGE4_smallwidth_large_r_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hr : 18 ≤ pair12Count S.D) (hw : pair13Count S.D+pair23Count S.D ≤ 12) :
    fullTarget S ≤ S.m := by
  have hb := le_trans (fullSupport_symbolic_BW_capacity_lower S hg hf ho (by omega))
    (fullSupport_symbolic_BW_lower S hg hf ho)
  have hsq := tge4_large_r_square _ _ _ _ hr hw hb
  rw [fullTarget_eq_square]
  omega

theorem fullSupport_variable_threshold_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hsum : 8 ≤ pair13Count S.D+pair23Count S.D)
    (hr : 2*(pair13Count S.D+pair23Count S.D) ≤ pair12Count S.D+6) :
    fullTarget S ≤ S.m := by
  have hb := le_trans (fullSupport_symbolic_BW_capacity_lower S hg hf ho (by omega))
    (fullSupport_symbolic_BW_lower S hg hf ho)
  have hsq := tge4_variable_threshold_square _ _ _ _ hsum hr hb
  rw [fullTarget_eq_square]
  omega

theorem fullSupport_tGE4_large_r_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : 4 ≤ pair23Count S.D) (hr : 18 ≤ pair12Count S.D) : fullTarget S ≤ S.m := by
  by_cases hc : (pair23Count S.D=4 ∧ 9 ≤ pair13Count S.D) ∨
      (pair23Count S.D=5 ∧ 7 ≤ pair13Count S.D) ∨
      (pair23Count S.D=6 ∧ 7 ≤ pair13Count S.D) ∨ 7 ≤ pair23Count S.D
  · exact le_of_lt (fullSupport_large_t_strict S hg hf ho hc)
  · exact fullSupport_tGE4_smallwidth_large_r_sharp S hg hf ho hr (by
      have := ho.1; omega)

theorem fullSupport_tGE4_reduced_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : 4 ≤ pair23Count S.D) :
    fullTarget S ≤ S.m ∨ (pair12Count S.D ≤ 17 ∧
      pair12Count S.D+6 < 2*(pair13Count S.D+pair23Count S.D) ∧
      ((pair23Count S.D=4 ∧ pair13Count S.D ≤ 8) ∨
       (pair23Count S.D=5 ∧ pair13Count S.D ≤ 6) ∨
       (pair23Count S.D=6 ∧ pair13Count S.D=6))) := by
  by_cases hc : (pair23Count S.D=4 ∧ 9 ≤ pair13Count S.D) ∨
      (pair23Count S.D=5 ∧ 7 ≤ pair13Count S.D) ∨
      (pair23Count S.D=6 ∧ 7 ≤ pair13Count S.D) ∨ 7 ≤ pair23Count S.D
  · exact Or.inl (le_of_lt (fullSupport_large_t_strict S hg hf ho hc))
  by_cases hr : 18 ≤ pair12Count S.D
  · exact Or.inl (fullSupport_tGE4_large_r_symbolic_sharp S hg hf ho ht hr)
  by_cases hv : 2*(pair13Count S.D+pair23Count S.D) ≤ pair12Count S.D+6
  · exact Or.inl (fullSupport_variable_threshold_symbolic_sharp S hg hf ho
      (by have := ho.1; omega) hv)
  · right
    have := ho.1
    omega

end NSP3
