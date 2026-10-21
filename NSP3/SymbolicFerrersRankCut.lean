import NSP3.SymbolicFerrersGap

namespace NSP3.Ferrers
open Finset

/-- Prefix/suffix charging uses each linear resource once; every cross pair
    lies in the ordered upper triangle. -/
theorem gap_cut_lower (r l : ℕ) (u v : ℕ → ℕ) (hl : l ≤ r) :
    (r-l)*(range (l+1)).sum u+l*(Ico l (r+1)).sum v+
      (range (l+1)).sum u*(Ico l (r+1)).sum v ≤
    (range (r+1)).sum (fun i => (r-i)*u i)+
      (range (r+1)).sum (fun j => j*v j)+
      (range (r+1)).sum (fun i =>
        ((range (r+1)).filter (fun j => i ≤ j)).sum (fun j => u i*v j)) := by
  have hpref : range (l+1) ⊆ range (r+1) := range_mono (by omega)
  have hsuf : Ico l (r+1) ⊆ range (r+1) := by
    intro j hj
    exact mem_range.mpr (mem_Ico.mp hj).2
  have hU : (r-l)*(range (l+1)).sum u ≤
      (range (r+1)).sum (fun i => (r-i)*u i) := by
    rw [mul_sum]
    apply le_trans (sum_le_sum ?_) (sum_le_sum_of_subset hpref)
    intro i hi
    apply Nat.mul_le_mul_right
    have := mem_range.mp hi
    omega
  have hV : l*(Ico l (r+1)).sum v ≤ (range (r+1)).sum (fun j => j*v j) := by
    rw [mul_sum]
    apply le_trans (sum_le_sum ?_) (sum_le_sum_of_subset hsuf)
    intro j hj
    exact Nat.mul_le_mul_right (v j) (mem_Ico.mp hj).1
  have hUV : (range (l+1)).sum u*(Ico l (r+1)).sum v ≤
      (range (r+1)).sum (fun i =>
        ((range (r+1)).filter (fun j => i ≤ j)).sum (fun j => u i*v j)) := by
    rw [sum_mul]
    apply le_trans (sum_le_sum ?_) (sum_le_sum_of_subset hpref)
    intro i hi
    rw [mul_sum]
    apply sum_le_sum_of_subset
    intro j hj
    apply mem_filter.mpr
    exact ⟨hsuf hj,by have := mem_range.mp hi; have := (mem_Ico.mp hj).1; omega⟩
  omega

/-- Geometric rank cut for an actual positive standard face. -/
theorem pair_plane_face_rank_lower (S : CyclicStaircase) {A B : ℕ}
    (_hA : 0<A) (_hB : 0<B) (hm : Point3.mk A B 0 ∈ S.D) :
    Nat.choose (pair12Count S.D) 2+rankCutPhi (pair12Count S.D) A B ≤
      (plane12PosFinset S).card := by
  have hAX : A < pure1Intercept S := (pure1_axis_mem_iff S _).mp
    (S.down_closed (b := Point3.mk A B 0) ⟨le_rfl,Nat.zero_le _,le_rfl⟩ hm)
  obtain ⟨l,hl,hlo,hup⟩ := exists_strip_index (cornerX_zero S)
    (show A < cornerX S (pair12Count S.D+1) by simpa using hAX)
  have hlr : l ≤ pair12Count S.D := by omega
  have hBY : B < cornerY S l := (pair12_strip_mem_iff S hlr hlo hup).mp hm
  let U := (range (l+1)).sum (gapU S)
  let V := (Ico l (pair12Count S.D+1)).sum (gapV S)
  have hU : A-l ≤ U := by
    have hpre := gapU_prefix S (k := l+1) (by omega)
    change U+(l+1)=cornerX S (l+1) at hpre
    omega
  have hV : B+l-pair12Count S.D ≤ V := by
    have hsuf := cornerY_suffix S (i := l) (by omega)
    rw [range_filter_ge,sum_add_distrib] at hsuf
    simp only [sum_const,Nat.card_Ico,smul_eq_mul,mul_one] at hsuf
    change cornerY S l = (pair12Count S.D+1-l)+V at hsuf
    omega
  have hcost : rankCutCost (pair12Count S.D) A B l ≤
      (pair12Count S.D-l)*U+l*V+U*V := by
    unfold rankCutCost
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hU)
      (Nat.mul_le_mul_left _ hV)) (Nat.mul_le_mul hU hV)
  have hcut := gap_cut_lower (pair12Count S.D) l (gapU S) (gapV S) hlr
  have hphi := rankCutPhi_le_cost (A := A) (B := B) hlr
  have harea := pair_plane_exact_gap_card S
  dsimp only [U,V] at hcost
  omega

theorem pair12_face_first_diagonal_lower (S : CyclicStaircase) {A B : ℕ}
    (hA : 0<A) (hB : 0<B) (hm : Point3.mk A B 0 ∈ S.D)
    (hdiag : A+B=pair12Count S.D+1) :
    Nat.choose (pair12Count S.D) 2+min A B ≤ (plane12PosFinset S).card := by
  have h := pair_plane_face_rank_lower S hA hB hm
  rw [rankCutPhi_first_diagonal hA hB hdiag] at h
  exact h

end NSP3.Ferrers
