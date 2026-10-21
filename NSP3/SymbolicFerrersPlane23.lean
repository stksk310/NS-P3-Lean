import NSP3.SymbolicFerrersArea23
import NSP3.SymbolicFerrersRankCut
import NSP3.SymbolicThreePlaneTerminal

namespace NSP3.Ferrers23
open Finset Ferrers

theorem cornerY_suffix (S : CyclicStaircase) {i : ℕ} (hi : i ≤ pair23Count S.D+1) :
    cornerY S i = ((range (pair23Count S.D+1)).filter (fun j => i ≤ j)).sum
      (fun j => 1+gapV S j) := by
  rw [range_filter_ge,sum_add_distrib]
  simp only [sum_const,Nat.card_Ico,smul_eq_mul,mul_one]
  have htotal := gapV_prefix S (k := pair23Count S.D+1) le_rfl
  rw [cornerY_last] at htotal
  have hpre := gapV_prefix S hi
  have hsplit := sum_range_add_sum_Ico (gapV S) hi
  change (range i).sum (gapV S)+(Ico i (pair23Count S.D+1)).sum (gapV S)=
    (range (pair23Count S.D+1)).sum (gapV S) at hsplit
  change cornerY S i = (pair23Count S.D+1-i)+(Ico i (pair23Count S.D+1)).sum (gapV S)
  omega

theorem full_plane_upperSum (S : CyclicStaircase) :
    (pair23PlaneSection S.D).card = upperSum (pair23Count S.D+1)
      (fun i j => (1+gapU S i)*(1+gapV S j)) := by
  rw [pair23_full_plane_card]
  unfold upperSum
  apply sum_congr rfl
  intro i hi
  have hir : i ≤ pair23Count S.D := by have := mem_range.mp hi; omega
  have hxstep := gapU_step S hir
  have hx : cornerX S (i+1)-cornerX S i=1+gapU S i := by omega
  rw [hx,cornerY_suffix S (by omega),mul_sum,sum_filter]

/-- Actual positive plane area: the exact frozen gap expansion, with no
    triangular-plane or residue-unit hypothesis. -/
theorem pair_plane_exact_gap_card (S : CyclicStaircase) :
    (plane23PosFinset S).card = Nat.choose (pair23Count S.D) 2+
      (range (pair23Count S.D+1)).sum (fun i => (pair23Count S.D-i)*gapU S i)+
      (range (pair23Count S.D+1)).sum (fun j => j*gapV S j)+
      (range (pair23Count S.D+1)).sum (fun i =>
        ((range (pair23Count S.D+1)).filter (fun j => i ≤ j)).sum
          (fun j => gapU S i*gapV S j)) := by
  have harea := full_plane_upperSum S
  rw [upperSum_expand] at harea
  have haxes := pair23_remove_axes S
  have hX := gapU_prefix S (k := pair23Count S.D+1) le_rfl
  have hY := gapV_prefix S (k := pair23Count S.D+1) le_rfl
  rw [cornerX_last] at hX
  rw [cornerY_last] at hY
  have hchoose : Nat.choose (pair23Count S.D+1) 2 =
      Nat.choose (pair23Count S.D) 2+pair23Count S.D := by
    rw [Nat.choose_succ_succ]; simp [Nat.add_comm]
  have hU : (range (pair23Count S.D+1)).sum (fun i => (pair23Count S.D+1-i)*gapU S i) =
      (range (pair23Count S.D+1)).sum (fun i => (pair23Count S.D-i)*gapU S i)+
        (range (pair23Count S.D+1)).sum (gapU S) := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    have hi' : i ≤ pair23Count S.D := by have := mem_range.mp hi; omega
    have he : pair23Count S.D+1-i=(pair23Count S.D-i)+1 := by omega
    rw [he,add_mul,one_mul]
  have hV : (range (pair23Count S.D+1)).sum (fun j => (j+1)*gapV S j) =
      (range (pair23Count S.D+1)).sum (fun j => j*gapV S j)+
        (range (pair23Count S.D+1)).sum (gapV S) := by
    simp only [add_mul,one_mul,sum_add_distrib]
  rw [hchoose,hU,hV] at harea
  have hcross : upperSum (pair23Count S.D+1) (fun i j => gapU S i*gapV S j) =
      (range (pair23Count S.D+1)).sum (fun i =>
        ((range (pair23Count S.D+1)).filter (fun j => i ≤ j)).sum
          (fun j => gapU S i*gapV S j)) := by simp only [upperSum,sum_filter]
  rw [hcross] at harea
  omega

/-- Geometric rank cut for an actual positive standard face. -/
theorem pair_plane_face_rank_lower (S : CyclicStaircase) {A B : ℕ}
    (_hA : 0<A) (_hB : 0<B) (hm : Point3.mk 0 A B ∈ S.D) :
    Nat.choose (pair23Count S.D) 2+rankCutPhi (pair23Count S.D) A B ≤
      (plane23PosFinset S).card := by
  have hAX : A < pure2Intercept S := (pure2_axis_mem_iff S _).mp
    (S.down_closed (b := Point3.mk 0 A B) ⟨le_rfl,le_rfl,Nat.zero_le _⟩ hm)
  obtain ⟨l,hl,hlo,hup⟩ := exists_strip_index (cornerX_zero S)
    (show A < cornerX S (pair23Count S.D+1) by simpa using hAX)
  have hlr : l ≤ pair23Count S.D := by omega
  have hBY : B < cornerY S l := (pair23_strip_mem_iff S hlr hlo hup).mp hm
  let U := (range (l+1)).sum (gapU S)
  let V := (Ico l (pair23Count S.D+1)).sum (gapV S)
  have hU : A-l ≤ U := by
    have hpre := gapU_prefix S (k := l+1) (by omega)
    change U+(l+1)=cornerX S (l+1) at hpre
    omega
  have hV : B+l-pair23Count S.D ≤ V := by
    have hsuf := cornerY_suffix S (i := l) (by omega)
    rw [range_filter_ge,sum_add_distrib] at hsuf
    simp only [sum_const,Nat.card_Ico,smul_eq_mul,mul_one] at hsuf
    change cornerY S l = (pair23Count S.D+1-l)+V at hsuf
    omega
  have hcost : rankCutCost (pair23Count S.D) A B l ≤
      (pair23Count S.D-l)*U+l*V+U*V := by
    unfold rankCutCost
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hU)
      (Nat.mul_le_mul_left _ hV)) (Nat.mul_le_mul hU hV)
  have hcut := gap_cut_lower (pair23Count S.D) l (gapU S) (gapV S) hlr
  have hphi := rankCutPhi_le_cost (A := A) (B := B) hlr
  have harea := pair_plane_exact_gap_card S
  dsimp only [U,V] at hcost
  omega

theorem pair23_face_first_diagonal_lower (S : CyclicStaircase) {A B : ℕ}
    (hA : 0<A) (hB : 0<B) (hm : Point3.mk 0 A B ∈ S.D)
    (hdiag : A+B=pair23Count S.D+1) :
    Nat.choose (pair23Count S.D) 2+min A B ≤ (plane23PosFinset S).card := by
  have h := pair_plane_face_rank_lower S hA hB hm
  rw [rankCutPhi_first_diagonal hA hB hdiag] at h
  exact h

theorem high_edge_gap (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) {i : ℕ}
    (hi : i ∈ Icc g.y (pair23Count S.D-g.z)) :
    g.y ≤ gapU S i ∨ g.z ≤ gapV S i := by
  have hie := mem_Icc.mp hi
  have hgx : 0 < g.y := hf.2.1
  have hgy : 0 < g.z := hf.2.2
  let a : Fin (pair23Count S.D) := ⟨i-1,by omega⟩
  let b : Fin (pair23Count S.D) := ⟨i,by omega⟩
  have horder : a < b := by change a.val < b.val; dsimp [a,b]; omega
  have hax := orderedPair23Boundary_y_baseline S a
  have hbx := orderedPair23Boundary_y_baseline S b
  have hay := orderedPair23Boundary_z_baseline S a
  have hby := orderedPair23Boundary_z_baseline S b
  change i-1+1 ≤ (orderedPair23Boundary S a).val.y at hax
  change i+1 ≤ (orderedPair23Boundary S b).val.y at hbx
  change pair23Count S.D-(i-1) ≤ (orderedPair23Boundary S a).val.z at hay
  change pair23Count S.D-i ≤ (orderedPair23Boundary S b).val.z at hby
  obtain h | h := pair23_terminal_rectangle_separation S hg hf
    (orderedPair23Boundary S a) (orderedPair23Boundary S b)
    (by omega) (by omega) (by omega) (by omega)
    (orderedPair23Boundary_y_strictMono S horder)
  · left
    have hea : a.val+1=i := by dsimp [a]; omega
    have heb : b.val+1=i+1 := rfl
    have hX0 := cornerX_inner S a
    have hX1 := cornerX_inner S b
    rw [hea] at hX0
    change cornerX S (i+1)=(orderedPair23Boundary S b).val.y at hX1
    unfold gapU
    rw [hX0,hX1]
    omega
  · right
    have hea : a.val+1=i := by dsimp [a]; omega
    have hY0 := cornerY_inner S a
    have hY1 := cornerY_inner S b
    rw [hea] at hY0
    change cornerY S (i+1)=(orderedPair23Boundary S b).val.z at hY1
    unfold gapV
    rw [hY0,hY1]
    omega

/-- The weighted Ferrers W bound in the actual pair23 orientation. -/
theorem pair23_weighted_gap_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    (Icc g.y (pair23Count S.D-g.z)).sum
      (fun i => min (g.y*(pair23Count S.D-i)) (g.z*i)) ≤ (pair23ExtraFinset S).card := by
  have hsub : Icc g.y (pair23Count S.D-g.z) ⊆ range (pair23Count S.D+1) := by
    intro i hi
    have := mem_Icc.mp hi
    have : 0 < g.z := hf.2.2
    apply mem_range.mpr
    omega
  have hlin : (Icc g.y (pair23Count S.D-g.z)).sum
      (fun i => min (g.y*(pair23Count S.D-i)) (g.z*i)) ≤
      (range (pair23Count S.D+1)).sum
        (fun i => (pair23Count S.D-i)*gapU S i+i*gapV S i) := by
    apply le_trans (sum_le_sum ?_) (sum_le_sum_of_subset hsub)
    intro i hi
    rcases high_edge_gap S hg hf hi with h | h
    · apply le_trans (min_le_left _ _)
      have := Nat.mul_le_mul_left (pair23Count S.D-i) h
      nlinarith
    · apply le_trans (min_le_right _ _)
      have := Nat.mul_le_mul_left i h
      nlinarith
  rw [sum_add_distrib] at hlin
  have harea := pair_plane_exact_gap_card S
  have hcard := card_plane23PosFinset S
  omega


end NSP3.Ferrers23

