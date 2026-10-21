import NSP3.SymbolicT3H11Integration

namespace NSP3
open Finset

/-- The exceptional one-unit family has three actual disjoint H rows. -/
theorem t3_one_unit_exception_H_lower (S : CyclicStaircase) {g : Point3}
    (ht : pair23Count S.D=3) (hr : 4≤pair12Count S.D)
    (hs : pair13Count S.D=pair12Count S.D-1)
    (hx : g.x=pair12Count S.D-1) (hy : g.y=2) (hz : g.z=1) :
    3*pair12Count S.D-6≤(fullSupportSymbolicH S g).card := by
  classical
  let R0:=(Icc 1 (pair12Count S.D-1)).image (fun x=>Point3.mk x 1 1)
  let R1:=(Icc 1 (pair12Count S.D-3)).image (fun x=>Point3.mk x 1 2)
  let R2:=(Icc 1 (pair12Count S.D-2)).image (fun x=>Point3.mk x 2 1)
  have h0 : R0⊆fullSupportSymbolicH S g := by
    intro p hp
    obtain ⟨x,hx',rfl⟩:=mem_image.mp hp
    have hi:=mem_Icc.mp hx'
    apply mem_union.mpr;right
    refine mem_filter.mpr ⟨(mem_lowerBoxFinset _ _).mpr
      ⟨⟨by change x≤g.x;omega,by simp [hy],by simp [hz]⟩,?_⟩,
      by simp [FullSupport];omega⟩
    intro heq
    have :=congrArg Point3.y heq
    change 1=g.y at this
    omega
  have h1 : R1⊆fullSupportSymbolicH S g := by
    intro p hp
    obtain ⟨x,hx',rfl⟩:=mem_image.mp hp
    have hi:=mem_Icc.mp hx'
    apply mem_union.mpr;left
    apply (mem_puncturedFullCoreFinset _ _ _).mpr
    refine ⟨?_,?_⟩
    · simp only [FullCore]
      exact ⟨by omega,by decide,by decide,by omega,by omega,by omega⟩
    · intro hle
      have :=hle.2.1;change g.y≤1 at this;omega
  have h2 : R2⊆fullSupportSymbolicH S g := by
    intro p hp
    obtain ⟨x,hx',rfl⟩:=mem_image.mp hp
    have hi:=mem_Icc.mp hx'
    apply mem_union.mpr;left
    apply (mem_puncturedFullCoreFinset _ _ _).mpr
    refine ⟨?_,?_⟩
    · simp only [FullCore]
      exact ⟨by omega,by decide,by decide,by omega,by omega,by omega⟩
    · intro hle
      have :=hle.1;change g.x≤x at this;omega
  have hd01 : Disjoint R0 R1 := by
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨x,_,rfl⟩:=mem_image.mp hp
    obtain ⟨y,_,heq⟩:=mem_image.mp hq
    have :=congrArg Point3.z heq
    norm_num at this
  have hd02 : Disjoint R0 R2 := by
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨x,_,rfl⟩:=mem_image.mp hp
    obtain ⟨y,_,heq⟩:=mem_image.mp hq
    have :=congrArg Point3.y heq
    norm_num at this
  have hd12 : Disjoint R1 R2 := by
    apply disjoint_left.mpr
    intro p hp hq
    obtain ⟨x,_,rfl⟩:=mem_image.mp hp
    obtain ⟨y,_,heq⟩:=mem_image.mp hq
    have :=congrArg Point3.y heq
    norm_num at this
  have c0 : R0.card=pair12Count S.D-1:=by
    dsimp [R0];rw [card_image_iff.mpr (fun _ _ _ _ heq=>congrArg Point3.x heq)];simp
  have c1 : R1.card=pair12Count S.D-3:=by
    dsimp [R1];rw [card_image_iff.mpr (fun _ _ _ _ heq=>congrArg Point3.x heq)];simp
  have c2 : R2.card=pair12Count S.D-2:=by
    dsimp [R2];rw [card_image_iff.mpr (fun _ _ _ _ heq=>congrArg Point3.x heq)];simp
  have hc:=card_le_card (union_subset (union_subset h0 h1) h2)
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hd02,hd12⟩),
    card_union_of_disjoint hd01,c0,c1,c2] at hc
  omega

/-- Rank-cut gives the extra plane unit; shared-axis gain is charged once. -/
theorem fullSupport_t3_one_unit_exception_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : 4≤pair12Count S.D) (hs : pair13Count S.D=pair12Count S.D-1)
    (hx : g.x=pair12Count S.D-1) (hy : g.y=2) (hz : g.z=1) :
    (pair12Count S.D+2)^2+1≤S.m := by
  have hH:=t3_one_unit_exception_H_lower S ht hr hs hx hy hz
  have hm:=fullSupport_axis_resource_lower S hg hf ho
  have hHcard:=symbolic_H_card S g
  have h12:=pair12_symbolic_defect_lower S hg hf
  have h13:=pair13_symbolic_defect_lower S hg hf
  have h23:=pair23_symbolic_defect_lower S hg hf
  have hp : rankCutPhi (pair12Count S.D) g.x g.y=2:=by
    rw [rankCutPhi_first_diagonal hf.1 hf.2.1 (by omega),hx,hy]
    omega
  have he12 : 2≤(pair12ExtraFinset S).card:=by omega
  have he13 : 1≤(pair13ExtraFinset S).card:=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h13
  have hd23 : 2≤ferrersPlaneDefect (pair23Count S.D) g.y g.z:=by
    rw [ht,hy,hz];decide
  have he23 : 2≤(pair23ExtraFinset S).card:=by omega
  have hGain : 1≤fullSupportAxisGain S g:=by
    unfold fullSupportAxisGain jointAxisGain
    rw [hx,hy,hz,hs,ht]
    simp only [max_eq_left (by omega : pair12Count S.D-1≤pair12Count S.D),
      max_eq_left (by omega : 2≤pair12Count S.D),
      max_eq_left (by omega : 1≤pair12Count S.D)]
    omega
  rw [hx,hy,hz,hs,ht] at hm
  simp only [max_eq_left (by omega : pair12Count S.D-1≤pair12Count S.D),
    max_eq_left (by omega : 2≤pair12Count S.D),
    max_eq_left (by omega : 1≤pair12Count S.D)] at hm
  have hc3 : Nat.choose 3 2=3:=by decide
  rw [hc3] at hm
  have hbase : Nat.choose (pair12Count S.D) 2+Nat.choose (pair12Count S.D-1) 2+
      6*pair12Count S.D+4≤S.m:=by omega
  have cr : 2*Nat.choose (pair12Count S.D) 2=
      pair12Count S.D*(pair12Count S.D-1):=by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (pair12Count S.D).two_dvd_mul_sub_one
  have cs : 2*Nat.choose (pair12Count S.D-1) 2=
      (pair12Count S.D-1)*(pair12Count S.D-1-1):=by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (pair12Count S.D-1).two_dvd_mul_sub_one
  have e1 : pair12Count S.D-1+1=pair12Count S.D:=by omega
  have e2 : pair12Count S.D-1-1+2=pair12Count S.D:=by omega
  nlinarith only [hbase,cr,cs,e1,e2]

/-- The infinite (r,r-1,3),(r-1,2,1) family closes symbolically, r>=4. -/
theorem fullSupport_t3_one_unit_exception_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : 4≤pair12Count S.D) (hs : pair13Count S.D=pair12Count S.D-1)
    (hx : g.x=pair12Count S.D-1) (hy : g.y=2) (hz : g.z=1) : fullTarget S≤S.m := by
  have hm:=fullSupport_t3_one_unit_exception_lower S hg hf ho ht hr hs hx hy hz
  have e : pair12Count S.D-1+1=pair12Count S.D:=by omega
  have hsq : (pair12Count S.D+pair13Count S.D+5)^2≤4*S.m:=by
    rw [hs];nlinarith only [hm,e]
  rw [fullTarget_eq_square,ht]
  norm_num only [Nat.add_assoc] at *
  omega

end NSP3
