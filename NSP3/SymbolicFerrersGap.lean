import NSP3.SymbolicFerrersArea
import NSP3.SymbolicFerrersAlgebra

namespace NSP3.Ferrers
open Finset

theorem cornerY_suffix (S : CyclicStaircase) {i : ℕ} (hi : i ≤ pair12Count S.D+1) :
    cornerY S i = ((range (pair12Count S.D+1)).filter (fun j => i ≤ j)).sum
      (fun j => 1+gapV S j) := by
  rw [range_filter_ge,sum_add_distrib]
  simp only [sum_const,Nat.card_Ico,smul_eq_mul,mul_one]
  have htotal := gapV_prefix S (k := pair12Count S.D+1) le_rfl
  rw [cornerY_last] at htotal
  have hpre := gapV_prefix S hi
  have hsplit := sum_range_add_sum_Ico (gapV S) hi
  change (range i).sum (gapV S)+(Ico i (pair12Count S.D+1)).sum (gapV S)=
    (range (pair12Count S.D+1)).sum (gapV S) at hsplit
  change cornerY S i = (pair12Count S.D+1-i)+(Ico i (pair12Count S.D+1)).sum (gapV S)
  omega

theorem full_plane_upperSum (S : CyclicStaircase) :
    (pair12PlaneSection S.D).card = upperSum (pair12Count S.D+1)
      (fun i j => (1+gapU S i)*(1+gapV S j)) := by
  rw [pair12_full_plane_card]
  unfold upperSum
  apply sum_congr rfl
  intro i hi
  have hir : i ≤ pair12Count S.D := by have := mem_range.mp hi; omega
  have hxstep := gapU_step S hir
  have hx : cornerX S (i+1)-cornerX S i=1+gapU S i := by omega
  rw [hx,cornerY_suffix S (by omega),mul_sum,sum_filter]

/-- Actual positive plane area: the exact frozen gap expansion, with no
    triangular-plane or residue-unit hypothesis. -/
theorem pair_plane_exact_gap_card (S : CyclicStaircase) :
    (plane12PosFinset S).card = Nat.choose (pair12Count S.D) 2+
      (range (pair12Count S.D+1)).sum (fun i => (pair12Count S.D-i)*gapU S i)+
      (range (pair12Count S.D+1)).sum (fun j => j*gapV S j)+
      (range (pair12Count S.D+1)).sum (fun i =>
        ((range (pair12Count S.D+1)).filter (fun j => i ≤ j)).sum
          (fun j => gapU S i*gapV S j)) := by
  have harea := full_plane_upperSum S
  rw [upperSum_expand] at harea
  have haxes := pair12_remove_axes S
  have hX := gapU_prefix S (k := pair12Count S.D+1) le_rfl
  have hY := gapV_prefix S (k := pair12Count S.D+1) le_rfl
  rw [cornerX_last] at hX
  rw [cornerY_last] at hY
  have hchoose : Nat.choose (pair12Count S.D+1) 2 =
      Nat.choose (pair12Count S.D) 2+pair12Count S.D := by
    rw [Nat.choose_succ_succ]; simp [Nat.add_comm]
  have hU : (range (pair12Count S.D+1)).sum (fun i => (pair12Count S.D+1-i)*gapU S i) =
      (range (pair12Count S.D+1)).sum (fun i => (pair12Count S.D-i)*gapU S i)+
        (range (pair12Count S.D+1)).sum (gapU S) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ pair12Count S.D := by have := mem_range.mp hi; omega
    have he : pair12Count S.D+1-i=(pair12Count S.D-i)+1 := by omega
    rw [he,add_mul,one_mul]
  have hV : (range (pair12Count S.D+1)).sum (fun j => (j+1)*gapV S j) =
      (range (pair12Count S.D+1)).sum (fun j => j*gapV S j)+
        (range (pair12Count S.D+1)).sum (gapV S) := by
    simp only [add_mul,one_mul,sum_add_distrib]
  rw [hchoose,hU,hV] at harea
  have hcross : upperSum (pair12Count S.D+1) (fun i j => gapU S i*gapV S j) =
      (range (pair12Count S.D+1)).sum (fun i =>
        ((range (pair12Count S.D+1)).filter (fun j => i ≤ j)).sum
          (fun j => gapU S i*gapV S j)) := by simp only [upperSum,sum_filter]
  rw [hcross] at harea
  omega

end NSP3.Ferrers
