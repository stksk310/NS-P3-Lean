import NSP3.SymbolicT2Profiles

namespace NSP3
open Finset

private theorem rectangle_two (A B : ℕ) (hA : 0<A) (hB : 0<B) :
    (ferrersRectangle 2 A B).card=A*B-1 := by
  classical
  have he : ferrersRectangle 2 A B = ((Icc 1 A).product (Icc 1 B)).erase (1,1) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hprod,hs⟩:=mem_filter.mp hp
      refine mem_erase.mpr ⟨?_,hprod⟩
      intro he
      subst p
      omega
    · intro hp
      obtain ⟨hne,hprod⟩:=mem_erase.mp hp
      obtain ⟨ha,hb⟩:=mem_product.mp hprod
      have ha':=mem_Icc.mp ha
      have hb':=mem_Icc.mp hb
      refine mem_filter.mpr ⟨hprod,?_⟩
      by_contra hn
      have he : p=(1,1):=Prod.ext (by omega) (by omega)
      exact hne he
  rw [he,card_erase_of_mem (by simp; omega)]
  simp

private theorem xunit_bw (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2) (hx : g.x=1) :
    3*pair12Count S.D+Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+2*(g.y*g.z)+2≤S.m := by
  have h:=fullSupport_symbolic_BW_lower S hg hf ho
  have hH:=positive_box_H_lower S g hf
  have hp:=Nat.mul_pos hf.2.1 hf.2.2
  have he:=rectangle_two g.y g.z hf.2.1 hf.2.2
  have hD : (ferrersRectangle 2 g.y g.z).card≤ferrersPlaneDefect 2 g.y g.z :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have h12 : 1≤ferrersPlaneDefect (pair12Count S.D) g.x g.y:=le_max_left _ _
  have h13 : 1≤ferrersPlaneDefect (pair13Count S.D) g.x g.z:=le_max_left _ _
  have hX:=le_max_left (pair12Count S.D) g.x
  have hY:=le_max_left (pair12Count S.D) g.y
  have hZ:=le_max_left (pair12Count S.D) g.z
  unfold fullSupportSymbolicBW at h
  rw [ht] at h
  rw [hx] at h12 h13 hX
  norm_num only [hx,one_mul,Nat.choose_self] at hH h
  omega

private theorem xunit_arithmetic (r s P : ℕ) (hr : 3 ≤ r) (hs : 2 ≤ s)
    (ho : s ≤ r) (hp : 2*(r-1)≤P) :
    ((r+s+4)^2+3)/4≤3*r+Nat.choose r 2+Nat.choose s 2+2*P+2 := by
  have cr : 2*Nat.choose r 2=r*(r-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2=s*(s-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r:=by omega
  have es : s-1+1=s:=by omega
  have ed : r-s+s=r:=Nat.sub_add_cancel ho
  have hn : (r+s+4)^2≤4*(3*r+Nat.choose r 2+Nat.choose s 2+2*P+2) := by
    nlinarith [Nat.zero_le ((r-s)^2)]
  omega

/-- With x=1, the actual yz rectangle and positive box supply two disjoint budgets. -/
theorem fullSupport_t2_x_unit_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hx : g.x=1) (hy : 2≤g.y) (hz : 2≤g.z) : fullTarget S≤S.m := by
  have hs : 2≤pair13Count S.D:=by have:=ho.1;omega
  by_cases hr : 3≤pair12Count S.D
  · have hcap:=pair12_terminal_return_capacity_ordered S hg hf ho
    rw [hx] at hcap
    have hB : g.y-2+2=g.y:=by omega
    have hC : g.z-2+2=g.z:=by omega
    have hp : 2*(pair12Count S.D-1)≤g.y*g.z := by
      have he : pair12Count S.D-1+1=pair12Count S.D:=by omega
      nlinarith [Nat.zero_le ((g.y-2)*(g.z-2))]
    have ha:=xunit_arithmetic (pair12Count S.D) (pair13Count S.D) (g.y*g.z)
      hr hs ho.2 hp
    have hb:=xunit_bw S hg hf ho ht hx
    rw [fullTarget_eq_square,ht]
    exact le_trans (by simpa only [Nat.add_assoc] using ha) hb
  · have hr2 : pair12Count S.D=2:=by have:=ho.2;omega
    have hs2 : pair13Count S.D=2:=by have:=ho.2;omega
    have hb:=card_le_card (lowerBoxFinset_subset_D hg)
    rw [card_lowerBoxFinset,S.card_D,hx] at hb
    rw [Nat.mul_assoc] at hb
    have hp:=Nat.mul_le_mul (show 3≤g.y+1 by omega) (show 3≤g.z+1 by omega)
    rw [fullTarget_eq_square,hr2,hs2,ht]
    norm_num
    norm_num only at hb hp
    omega

private theorem pair12_two_axes (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair12Count S.D=2) : 7≤pure1Intercept S+pure2Intercept S := by
  classical
  have hX:=pair12_intercept1_lower S
  have hY:=pair12_intercept2_lower S
  have hdef:=pair12_symbolic_defect_lower S hg hf
  have h1 : 1≤ferrersPlaneDefect (pair12Count S.D) g.x g.y:=le_max_left _ _
  by_contra hn
  have heX : pure1Intercept S=3:=by omega
  have heY : pure2Intercept S=3:=by omega
  have hU:=Ferrers.gapU_prefix S (k:=3) (by omega)
  have hV:=Ferrers.gapV_prefix S (k:=3) (by omega)
  have hlastX : Ferrers.cornerX S 3=3:=by simpa only [ht,heX] using Ferrers.cornerX_last S
  have hlastY : Ferrers.cornerY S 3=0:=by simpa only [ht] using Ferrers.cornerY_last S
  have hu0 : (range 3).sum (Ferrers.gapU S)=0:=by omega
  have hv0 : (range 3).sum (Ferrers.gapV S)=0:=by omega
  have hu : ∀ i∈range 3,Ferrers.gapU S i=0:=sum_eq_zero_iff.mp hu0
  have hv : ∀ i∈range 3,Ferrers.gapV S i=0:=sum_eq_zero_iff.mp hv0
  have ha:=Ferrers.pair_plane_exact_gap_card S
  rw [ht] at ha
  have huL : (range 3).sum (fun i=>(2-i)*Ferrers.gapU S i)=0:=
    sum_eq_zero (fun i hi=>by rw [hu i hi,mul_zero])
  have hvL : (range 3).sum (fun j=>j*Ferrers.gapV S j)=0:=
    sum_eq_zero (fun j hj=>by rw [hv j hj,mul_zero])
  have hcross : (range 3).sum (fun i=>((range 3).filter (fun j=>i≤j)).sum
      (fun j=>Ferrers.gapU S i*Ferrers.gapV S j))=0:=by
    apply sum_eq_zero
    intro i hi
    simp only [hu i hi,zero_mul,sum_const_zero]
  rw [huL,hvL,hcross] at ha
  have hc:=card_plane12PosFinset S
  rw [ht] at hc
  norm_num at ha hc
  omega

private theorem pair13_two_axes (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair13Count S.D=2) : 7≤pure1Intercept S+pure3Intercept S := by
  classical
  have hX:=pair13_intercept1_lower S
  have hZ:=pair13_intercept3_lower S
  have hdef:=pair13_symbolic_defect_lower S hg hf
  have h1 : 1≤ferrersPlaneDefect (pair13Count S.D) g.x g.z:=le_max_left _ _
  by_contra hn
  have heX : pure1Intercept S=3:=by omega
  have heZ : pure3Intercept S=3:=by omega
  have hU:=Ferrers13.gapU_prefix S (k:=3) (by omega)
  have hV:=Ferrers13.gapV_prefix S (k:=3) (by omega)
  have hlastX : Ferrers13.cornerX S 3=3:=by simpa only [ht,heX] using Ferrers13.cornerX_last S
  have hlastY : Ferrers13.cornerY S 3=0:=by simpa only [ht] using Ferrers13.cornerY_last S
  have hu0 : (range 3).sum (Ferrers13.gapU S)=0:=by omega
  have hv0 : (range 3).sum (Ferrers13.gapV S)=0:=by omega
  have hu : ∀ i∈range 3,Ferrers13.gapU S i=0:=sum_eq_zero_iff.mp hu0
  have hv : ∀ i∈range 3,Ferrers13.gapV S i=0:=sum_eq_zero_iff.mp hv0
  have ha:=Ferrers13.pair_plane_exact_gap_card S
  rw [ht] at ha
  have huL : (range 3).sum (fun i=>(2-i)*Ferrers13.gapU S i)=0:=
    sum_eq_zero (fun i hi=>by rw [hu i hi,mul_zero])
  have hvL : (range 3).sum (fun j=>j*Ferrers13.gapV S j)=0:=
    sum_eq_zero (fun j hj=>by rw [hv j hj,mul_zero])
  have hcross : (range 3).sum (fun i=>((range 3).filter (fun j=>i≤j)).sum
      (fun j=>Ferrers13.gapU S i*Ferrers13.gapV S j))=0:=by
    apply sum_eq_zero
    intro i hi
    simp only [hu i hi,zero_mul,sum_const_zero]
  rw [huL,hvL,hcross] at ha
  have hc:=card_plane13PosFinset S
  rw [ht] at hc
  norm_num at ha hc
  omega

/-- All three exact two-corner planes force enough distinct axis/face/full resources. -/
theorem fullSupport_t2_all_pair_two_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hr : pair12Count S.D=2) (hs : pair13Count S.D=2) : fullTarget S≤S.m := by
  classical
  have hxy:=pair12_two_axes S hg hf hr
  have hxz:=pair13_two_axes S hg hf hs
  have hyz:=thin23_t2_transverse_axis_unit S hg hf ht
  have h12:=pair12_symbolic_defect_lower S hg hf
  have h13:=pair13_symbolic_defect_lower S hg hf
  have h23:=pair23_symbolic_defect_lower S hg hf
  have h12one : 1≤ferrersPlaneDefect (pair12Count S.D) g.x g.y:=le_max_left _ _
  have h13one : 1≤ferrersPlaneDefect (pair13Count S.D) g.x g.z:=le_max_left _ _
  have h23one : 1≤ferrersPlaneDefect (pair23Count S.D) g.y g.z:=le_max_left _ _
  have hcap:=pair12_terminal_return_capacity_ordered S hg hf ho
  have hp : Point3.mk 1 1 1∈fullSupportSymbolicH S g := by
    apply mem_union.mpr;right
    apply mem_filter.mpr
    refine ⟨(mem_lowerBoxFinset _ _).mpr ⟨⟨hf.1,hf.2.1,hf.2.2⟩,?_⟩,by simp [FullSupport]⟩
    intro he
    have hx:=congrArg Point3.x he
    have hy:=congrArg Point3.y he
    have hz:=congrArg Point3.z he
    simp only at hx hy hz
    omega
  have hH:=card_pos.mpr ⟨_,hp⟩
  have hb:=thin23_disjoint_resource_lower S hg hf
  rw [card_plane12PosFinset,card_plane13PosFinset,card_plane23PosFinset,hr,hs,ht] at hb
  norm_num at hb
  have hm : 16≤S.m:=by omega
  rw [fullTarget_eq_square,hr,hs,ht]
  norm_num
  exact hm

private theorem W_unit_lower (n A : ℕ) (hA : 1≤A) (hn : A<n) : A≤ferrersW n A 1 := by
  have hm : A∈Icc A (n-1):=mem_Icc.mpr ⟨le_rfl,by omega⟩
  have hs:=single_le_sum (f:=fun i=>min (A*(n-i)) (1*i))
    (fun _ _=>Nat.zero_le _) hm
  have hp:=Nat.mul_le_mul_left A (show 1≤n-A by omega)
  unfold ferrersW
  exact le_trans (le_min (by simpa using hp) (by simp)) hs

private theorem transverse_bw (S : CyclicStaircase) {g : Point3} (N n : ℕ)
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hp : (g.y=1 ∧ g.z=N ∧ n=pair12Count S.D) ∨
      (g.z=1 ∧ g.y=N ∧ n=pair13Count S.D)) :
    1+3*pair12Count S.D+Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+N*(g.x+1)+ferrersPlaneDefect n g.x 1≤S.m := by
  have h:=fullSupport_symbolic_BW_lower S hg hf ho
  have hH:=positive_box_H_lower S g hf
  have he:=rectangle_two g.y g.z hf.2.1 hf.2.2
  have hD : (ferrersRectangle 2 g.y g.z).card≤ferrersPlaneDefect 2 g.y g.z :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have h12 : 1≤ferrersPlaneDefect (pair12Count S.D) g.x g.y:=le_max_left _ _
  have h13 : 1≤ferrersPlaneDefect (pair13Count S.D) g.x g.z:=le_max_left _ _
  have hX:=le_max_left (pair12Count S.D) g.x
  have hY:=le_max_left (pair12Count S.D) g.y
  have hZ:=le_max_left (pair12Count S.D) g.z
  have hpos:=Nat.mul_pos (Nat.mul_pos hf.1 hf.2.1) hf.2.2
  unfold fullSupportSymbolicBW at h
  rw [ht] at h
  rcases hp with ⟨hy,rfl,rfl⟩ | ⟨hz,rfl,rfl⟩
  · simp only [hy,mul_one,one_mul] at hH he hD h12 h13 hX hY hZ hpos h
    norm_num only [Nat.choose_self] at h
    have hmul : g.z*(g.x+1)=g.x*g.z+g.z:=by ring
    rw [hmul]
    omega
  · simp only [hz,mul_one,one_mul] at hH he hD h12 h13 hX hY hZ hpos h
    norm_num only [Nat.choose_self] at h
    have hmul : g.y*(g.x+1)=g.x*g.y+g.y:=by ring
    rw [hmul]
    omega

private theorem transverse_arithmetic (r s A N D : ℕ)
    (hr : 3 ≤ r) (hs : 2 ≤ s) (ho : s ≤ r) (hA : 2≤A) (hN : 2≤N)
    (hcap : r+1≤A+N) (hD : 1≤D)
    (hW : r=s → A<r → A≤D)
    (hne : ¬(r=3 ∧ s=3 ∧ A=2 ∧ N=2)) :
    ((r+s+4)^2+3)/4≤1+3*r+Nat.choose r 2+Nat.choose s 2+N*(A+1)+D := by
  have eA : A-1+1=A:=by omega
  have eN : N-2+2=N:=by omega
  have hQ : 2*r≤N*(A+1) := by
    nlinarith [Nat.zero_le ((N-2)*(A-1))]
  have hgain : r=s → 2*r+3≤N*(A+1)+D := by
    intro he
    by_cases hAr : r≤A
    · nlinarith
    have hAD:=hW he (by omega)
    by_cases hAend : A=r-1
    · by_cases hr4 : 4≤r
      · omega
      · have hr3 : r=3:=by omega
        have hN3 : 3≤N:=by omega
        nlinarith
    have hAr2 : A≤r-2:=by omega
    have hr4 : 4≤r:=by omega
    have erA : r-A-1+A+1=r:=by omega
    have eA2 : A-2+2=A:=by omega
    have hmul:=Nat.mul_le_mul_right (A+1) hcap
    nlinarith [Nat.zero_le ((A-2)*(r-A-1))]
  have cr : 2*Nat.choose r 2=r*(r-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2=s*(s-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r:=by omega
  have es : s-1+1=s:=by omega
  have ed : r-s+s=r:=Nat.sub_add_cancel ho
  have hsq : (r+s+4)^2≤4*(1+3*r+Nat.choose r 2+Nat.choose s 2+N*(A+1)+D) := by
    by_cases he : r=s
    · have hg:=hgain he
      nlinarith only [cr,cs,er,es,hg,he]
    · have ha : 1≤r-s:=by omega
      nlinarith only [cr,cs,er,es,ed,ha,hQ,hD,Nat.zero_le ((r-s)^2)]
  omega

private theorem exceptional_transverse (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hr : pair12Count S.D=3) (hs : pair13Count S.D=3) (ht : pair23Count S.D=2)
    (hx : g.x=2) (hp : (g.y=1 ∧ g.z=2) ∨ (g.z=1 ∧ g.y=2)) : fullTarget S≤S.m := by
  have h:=fullSupport_symbolic_BF_lower S hg hf ho
  have hH:=positive_box_H_lower S g hf
  have hPhi : rankCutPhi 3 2 2=2 := by
    simpa using (rankCutPhi_first_diagonal (r:=3) (A:=2) (B:=2)
      (by decide) (by decide) (by decide))
  have hd22 : ferrersPlaneDefect 3 2 2=1:=by decide
  have hd21 : ferrersPlaneDefect 3 2 1=2:=by decide
  have hd12 : ferrersPlaneDefect 2 1 2=1:=by decide
  have hd2 : ferrersPlaneDefect 2 2 1=1:=by decide
  have haxis : fullSupportAxisGain S g=1 := by
    rcases hp with ⟨hy,hz⟩ | ⟨hz,hy⟩ <;>
      norm_num [fullSupportAxisGain,jointAxisGain,hr,hs,ht,hx,hy,hz]
  unfold fullSupportSymbolicBF fullSupportSymbolicBW at h
  rw [hr,hs,ht,hx,haxis] at h
  rw [hx] at hH
  rcases hp with ⟨hy,hz⟩ | ⟨hz,hy⟩
  · rw [hy,hz,hd21,hd22,hd12,hPhi] at h
    rw [hy,hz] at hH
    norm_num at h hH
    rw [fullTarget_eq_square,hr,hs,ht]
    norm_num
    omega
  · rw [hy,hz,hd22,hd21,hd2,hPhi] at h
    rw [hy,hz] at hH
    norm_num at h hH
    rw [fullTarget_eq_square,hr,hs,ht]
    norm_num
    omega

/-- Both transverse-unit orientations, with the genuine332 BF improvement. -/
theorem fullSupport_t2_transverse_unit_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hA : 2≤g.x) (hp : (g.y=1 ∧ 2≤g.z) ∨ (g.z=1 ∧ 2≤g.y)) : fullTarget S≤S.m := by
  have hs : 2≤pair13Count S.D:=by have:=ho.1;omega
  by_cases hr : 3≤pair12Count S.D
  · rcases hp with ⟨hy,hN⟩ | ⟨hz,hN⟩
    · by_cases hex : pair12Count S.D=3 ∧ pair13Count S.D=3 ∧ g.x=2 ∧ g.z=2
      · exact exceptional_transverse S hg hf ho hex.1 hex.2.1 ht hex.2.2.1 (Or.inl ⟨hy,hex.2.2.2⟩)
      have hcap:=pair12_terminal_return_capacity_ordered S hg hf ho
      rw [hy] at hcap
      have hb:=transverse_bw S g.z (pair12Count S.D) hg hf ho ht (Or.inl ⟨hy,rfl,rfl⟩)
      have ha:=transverse_arithmetic (pair12Count S.D) (pair13Count S.D) g.x g.z
        (ferrersPlaneDefect (pair12Count S.D) g.x 1) hr hs ho.2 hA hN (by omega)
        (le_max_left _ _) (by
          intro _ hh
          exact le_trans (W_unit_lower _ _ (by omega) hh)
            (le_trans (le_max_right _ _) (le_max_right _ _))) hex
      rw [fullTarget_eq_square,ht]
      exact le_trans (by simpa only [Nat.add_assoc] using ha) hb
    · by_cases hex : pair12Count S.D=3 ∧ pair13Count S.D=3 ∧ g.x=2 ∧ g.y=2
      · exact exceptional_transverse S hg hf ho hex.1 hex.2.1 ht hex.2.2.1 (Or.inr ⟨hz,hex.2.2.2⟩)
      have hcap:=pair12_terminal_return_capacity_ordered S hg hf ho
      rw [hz] at hcap
      have hb:=transverse_bw S g.y (pair13Count S.D) hg hf ho ht (Or.inr ⟨hz,rfl,rfl⟩)
      have ha:=transverse_arithmetic (pair12Count S.D) (pair13Count S.D) g.x g.y
        (ferrersPlaneDefect (pair13Count S.D) g.x 1) hr hs ho.2 hA hN (by omega)
        (le_max_left _ _) (by
          intro he hh
          rw [he] at hh
          exact le_trans (W_unit_lower _ _ (by omega) hh)
            (le_trans (le_max_right _ _) (le_max_right _ _))) hex
      rw [fullTarget_eq_square,ht]
      exact le_trans (by simpa only [Nat.add_assoc] using ha) hb
  · exact fullSupport_t2_all_pair_two_sharp S hg hf ho ht (by have:=ho.2;omega) (by have:=ho.2;omega)

end NSP3
