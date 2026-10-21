import NSP3.SymbolicThin23Sharp

namespace NSP3
open Finset

/-- A strict actual yz defect cannot coexist with two minimal intercepts. -/
theorem thin23_t2_transverse_axis_unit (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=2) : 7 ≤ pure2Intercept S+pure3Intercept S := by
  classical
  have hY := pair23_intercept2_lower S
  have hZ := pair23_intercept3_lower S
  have hdef := pair23_symbolic_defect_lower S hg hf
  have h1 : 1 ≤ ferrersPlaneDefect (pair23Count S.D) g.y g.z := le_max_left _ _
  by_contra hn
  have heY : pure2Intercept S=3 := by omega
  have heZ : pure3Intercept S=3 := by omega
  have hU := Ferrers23.gapU_prefix S (k := 3) (by omega)
  have hV := Ferrers23.gapV_prefix S (k := 3) (by omega)
  have hXlast : Ferrers23.cornerX S 3=3 := by
    simpa only [ht,heY] using Ferrers23.cornerX_last S
  have hYlast : Ferrers23.cornerY S 3=0 := by
    simpa only [ht] using Ferrers23.cornerY_last S
  have hU0 : (range 3).sum (Ferrers23.gapU S)=0 := by omega
  have hV0 : (range 3).sum (Ferrers23.gapV S)=0 := by omega
  have hu : ∀ i ∈ range 3, Ferrers23.gapU S i=0 := sum_eq_zero_iff.mp hU0
  have hv : ∀ i ∈ range 3, Ferrers23.gapV S i=0 := sum_eq_zero_iff.mp hV0
  have harea := Ferrers23.pair_plane_exact_gap_card S
  rw [ht] at harea
  have huLin : (range 3).sum (fun i => (2-i)*Ferrers23.gapU S i)=0 :=
    sum_eq_zero (fun i hi => by rw [hu i hi,mul_zero])
  have hvLin : (range 3).sum (fun j => j*Ferrers23.gapV S j)=0 :=
    sum_eq_zero (fun j hj => by rw [hv j hj,mul_zero])
  have hcross : (range 3).sum (fun i => ((range 3).filter (fun j => i ≤ j)).sum
      (fun j => Ferrers23.gapU S i*Ferrers23.gapV S j))=0 := by
    apply sum_eq_zero
    intro i hi
    simp only [hu i hi,zero_mul,sum_const_zero]
  rw [huLin,hvLin,hcross] at harea
  have hc := card_plane23PosFinset S
  rw [ht] at hc
  norm_num at harea hc
  omega

/-- The k=2 balanced endpoint follows from transverse-axis strictness. -/
theorem fullSupport_t2_h11_endpoint_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (_ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hr : pair12Count S.D=2) (hs : pair13Count S.D=2)
    (hx : g.x=2) (hy : g.y=1) (hz : g.z=1) :
    fullTarget S ≤ S.m := by
  classical
  have hj := long_face_axis_joint_unit S hg hf (by omega) (by omega) hy
  have hYz := thin23_t2_transverse_axis_unit S hg hf ht
  have h12 := pair12_symbolic_defect_lower S hg hf
  have h13 := pair13_symbolic_defect_lower S hg hf
  have h23 := pair23_symbolic_defect_lower S hg hf
  have h12one : 1 ≤ ferrersPlaneDefect (pair12Count S.D) g.x g.y := le_max_left _ _
  have h13one : 1 ≤ ferrersPlaneDefect (pair13Count S.D) g.x g.z := le_max_left _ _
  have h23one : 1 ≤ ferrersPlaneDefect (pair23Count S.D) g.y g.z := le_max_left _ _
  have hHmem : Point3.mk 1 1 1 ∈ fullSupportSymbolicH S g := by
    apply mem_union.mpr; right
    apply mem_filter.mpr
    refine ⟨(mem_lowerBoxFinset _ _).mpr ⟨⟨by simp [hx],by simp [hy],by simp [hz]⟩,?_⟩,
      by simp [FullSupport]⟩
    intro he
    have heX := congrArg Point3.x he
    simp [hx] at heX
  have hH := card_pos.mpr ⟨_,hHmem⟩
  have hxAxis : 3 ≤ pure1Intercept S := by
    have hh := pair12_intercept1_lower S
    omega
  have ha := thin23_disjoint_resource_lower S hg hf
  rw [card_plane12PosFinset,card_plane13PosFinset,card_plane23PosFinset,hr,hs,ht] at ha
  rw [hr,hx] at hj
  norm_num at ha hj
  have hm : 16 ≤ S.m := by omega
  rw [fullTarget_eq_square,hr,hs,ht]
  norm_num
  exact hm

/-- A hypothetical sharp failure is forced into the single balanced equality
    family. This is a reduction, not an exclusion of that family. -/
theorem thin23_failure_forces_balanced_equality (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hs : 2 ≤ pair13Count S.D) (hy : g.y=1) (hz : g.z=1)
    (hfail : S.m < fullTarget S) :
    pair12Count S.D=g.x ∧ pair13Count S.D=g.x ∧ 3 ≤ g.x ∧
      S.m=(g.x+1)*(g.x+3) := by
  have hcap := pair12_terminal_return_capacity_ordered S hg hf ho
  have hrs := ho.2
  have hnb : ¬ (pair13Count S.D < pair12Count S.D ∨ pair12Count S.D < g.x) := by
    intro hn
    have hsharp := fullSupport_t2_h11_nonbalanced_sharp S hg hf ho ht hs hy hz hn
    omega
  have hrEq : pair12Count S.D=g.x := by omega
  have hsEq : pair13Count S.D=g.x := by omega
  have hk : 3 ≤ g.x := by
    by_contra hn
    have hx2 : g.x=2 := by omega
    have hr2 : pair12Count S.D=2 := by omega
    have hs2 : pair13Count S.D=2 := by omega
    have hsharp := fullSupport_t2_h11_endpoint_sharp S hg hf ho ht hr2 hs2 hx2 hy hz
    omega
  have hb := fullSupport_t2_h11_lower S hg hf ho ht hs hy hz
  rw [hrEq,hsEq] at hb
  have hc : 2*Nat.choose g.x 2=g.x*(g.x-1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' g.x.two_dvd_mul_sub_one
  have he : g.x-1+1=g.x := by omega
  have hlow : (g.x+1)*(g.x+3) ≤ S.m := by nlinarith
  have htarget : fullTarget S=(g.x+2)^2 := by
    rw [fullTarget_eq_square,hrEq,hsEq,ht]
    have hpoly : (g.x+g.x+2+2)^2+3=4*(g.x+2)^2+3 := by ring
    rw [hpoly]
    omega
  rw [htarget] at hfail
  exact ⟨hrEq,hsEq,hk,by nlinarith⟩

end NSP3
