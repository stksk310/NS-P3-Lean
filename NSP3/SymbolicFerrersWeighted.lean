import NSP3.SymbolicFerrersGap
import NSP3.SymbolicTerminalRectangle

namespace NSP3.Ferrers
open Finset

theorem high_edge_gap (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) {i : ℕ}
    (hi : i ∈ Icc g.x (pair12Count S.D-g.y)) :
    g.x ≤ gapU S i ∨ g.y ≤ gapV S i := by
  have hie := mem_Icc.mp hi
  have hgx : 0 < g.x := hf.1
  have hgy : 0 < g.y := hf.2.1
  let a : Fin (pair12Count S.D) := ⟨i-1,by omega⟩
  let b : Fin (pair12Count S.D) := ⟨i,by omega⟩
  have horder : a < b := by change a.val < b.val; dsimp [a,b]; omega
  have hax := orderedPair12Boundary_x_baseline S a
  have hbx := orderedPair12Boundary_x_baseline S b
  have hay := orderedPair12Boundary_y_baseline S a
  have hby := orderedPair12Boundary_y_baseline S b
  change i-1+1 ≤ (orderedPair12Boundary S a).val.x at hax
  change i+1 ≤ (orderedPair12Boundary S b).val.x at hbx
  change pair12Count S.D-(i-1) ≤ (orderedPair12Boundary S a).val.y at hay
  change pair12Count S.D-i ≤ (orderedPair12Boundary S b).val.y at hby
  obtain h | h := pair12_terminal_rectangle_separation S hg hf
    (orderedPair12Boundary S a) (orderedPair12Boundary S b)
    (by omega) (by omega) (by omega) (by omega)
    (orderedPair12Boundary_x_strictMono S horder)
  · left
    have hea : a.val+1=i := by dsimp [a]; omega
    have heb : b.val+1=i+1 := rfl
    have hX0 := cornerX_inner S a
    have hX1 := cornerX_inner S b
    rw [hea] at hX0
    change cornerX S (i+1)=(orderedPair12Boundary S b).val.x at hX1
    unfold gapU
    rw [hX0,hX1]
    omega
  · right
    have hea : a.val+1=i := by dsimp [a]; omega
    have hY0 := cornerY_inner S a
    have hY1 := cornerY_inner S b
    rw [hea] at hY0
    change cornerY S (i+1)=(orderedPair12Boundary S b).val.y at hY1
    unfold gapV
    rw [hY0,hY1]
    omega

/-- The weighted Ferrers W bound in the actual pair12 orientation. -/
theorem pair12_weighted_gap_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    (Icc g.x (pair12Count S.D-g.y)).sum
      (fun i => min (g.x*(pair12Count S.D-i)) (g.y*i)) ≤ (pair12ExtraFinset S).card := by
  have hsub : Icc g.x (pair12Count S.D-g.y) ⊆ range (pair12Count S.D+1) := by
    intro i hi
    have := mem_Icc.mp hi
    have : 0 < g.y := hf.2.1
    apply mem_range.mpr
    omega
  have hlin : (Icc g.x (pair12Count S.D-g.y)).sum
      (fun i => min (g.x*(pair12Count S.D-i)) (g.y*i)) ≤
      (range (pair12Count S.D+1)).sum
        (fun i => (pair12Count S.D-i)*gapU S i+i*gapV S i) := by
    apply le_trans (sum_le_sum ?_) (sum_le_sum_of_subset hsub)
    intro i hi
    rcases high_edge_gap S hg hf hi with h | h
    · apply le_trans (min_le_left _ _)
      have := Nat.mul_le_mul_left (pair12Count S.D-i) h
      nlinarith
    · apply le_trans (min_le_right _ _)
      have := Nat.mul_le_mul_left i h
      nlinarith
  rw [sum_add_distrib] at hlin
  have harea := pair_plane_exact_gap_card S
  have hcard := card_plane12PosFinset S
  omega

end NSP3.Ferrers
