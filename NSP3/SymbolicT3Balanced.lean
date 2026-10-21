import NSP3.SymbolicT3Budget

namespace NSP3
open Finset

private theorem minimal_axis_extra (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (hr : 0 < pair12Count S.D) (hy : g.y=1)
    (hX : pure1Intercept S=g.x+1) :
    pair12Count S.D ≤ (pair12ExtraFinset S).card := by
  classical
  let r := pair12Count S.D
  let b := orderedPair12Boundary S (⟨r-1,by dsimp [r]; omega⟩ : Fin r)
  have hbX := (Ferrers.boundary_lt_intercepts S b).1
  have hrow : Point3.mk g.x 1 0 ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨le_rfl,by simp [hy],Nat.zero_le _⟩,
      by intro he; have hez := congrArg Point3.z he; have := hf.2.2; change 0=g.z at hez; omega⟩)
  have hbY : 2 ≤ b.val.y := by
    by_contra hn
    have hle : b.val ≤ Point3.mk g.x 1 0 :=
      ⟨by change b.val.x ≤ g.x; omega,by change b.val.y ≤ 1; omega,
        by simp [b.property.2.2.2]⟩
    exact b.property.1.not_mem (S.down_closed hle hrow)
  have hYr : Ferrers.cornerY S r=b.val.y := by
    have he : r-1+1=r := by omega
    simpa only [he] using Ferrers.cornerY_inner S (⟨r-1,by dsimp [r]; omega⟩ : Fin r)
  have hv : 1 ≤ Ferrers.gapV S r := by
    have hstep := Ferrers.gapV_step S (i := r) le_rfl
    have hlast := Ferrers.cornerY_last S
    change Ferrers.cornerY S (r+1)=0 at hlast
    omega
  have hV : r ≤ (range (r+1)).sum (fun j => j*Ferrers.gapV S j) := by
    have hs := single_le_sum (f := fun j => j*Ferrers.gapV S j)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr (show r<r+1 by omega))
    have hm := Nat.mul_le_mul_left r hv
    omega
  have harea := Ferrers.pair_plane_exact_gap_card S
  have hcard := card_plane12PosFinset S
  change (plane12PosFinset S).card = Nat.choose r 2+
    (range (r+1)).sum (fun i => (r-i)*Ferrers.gapU S i)+
    (range (r+1)).sum (fun j => j*Ferrers.gapV S j)+
    (range (r+1)).sum (fun i => ((range (r+1)).filter (fun j => i ≤ j)).sum
      (fun j => Ferrers.gapU S i*Ferrers.gapV S j)) at harea
  change (plane12PosFinset S).card=Nat.choose r 2+(pair12ExtraFinset S).card at hcard
  dsimp [r] at *
  omega

/-- Saturation is forced by disjoint actual resources, not by a candidate table. -/
theorem t3_balanced_k4_saturation (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (he : pair12Count S.D=pair13Count S.D)
    (hk : pair12Count S.D=4) (hh : g.x=4) (hy : g.y=1) (hz : g.z=1)
    (h13 : Point3.mk 0 1 3∈S.D) (h31 : Point3.mk 0 3 1∈S.D)
    (hm : S.m≤42) : S.m=42 ∧ pure1Intercept S=6 ∧
      pure2Intercept S=5 ∧ pure3Intercept S=5 ∧
      (pair12ExtraFinset S).card=1 ∧ (pair13ExtraFinset S).card=1 ∧
      (plane23PosFinset S).card=5 := by
  classical
  have hb:=t3_balanced_extra_budget S hg hf he (by omega) ht hy hz
    {Point3.mk 0 1 3,Point3.mk 0 3 1} (by
      intro p hp; simp only [mem_insert,mem_singleton] at hp
      rcases hp with rfl | rfl <;> norm_num <;> assumption)
  have hH:=t3_equal_height_H_lower S (g:=g) ht he (by omega) (by omega)
  have hX:=pair12_intercept1_lower S
  have hY:=pair12_intercept2_lower S
  have hZ:=pair12_return_capacity_fullSupport S hg hf
  have h12:=pair12_symbolic_defect_lower S hg hf
  have h13':=pair13_symbolic_defect_lower S hg hf
  have hD12 : 1≤ferrersPlaneDefect (pair12Count S.D) g.x g.y:=le_max_left _ _
  have hD13 : 1≤ferrersPlaneDefect (pair13Count S.D) g.x g.z:=le_max_left _ _
  have ha:=thin23_three_corner_area_lower S hg hf ht hy hz
  rw [card_plane12PosFinset,card_plane13PosFinset,←he,hk] at hb
  have hchoose : Nat.choose 4 2=6 := by decide
  rw [hchoose] at hb
  norm_num at hb
  have hXne : pure1Intercept S≠5 := by
    intro hXe
    have hx:=minimal_axis_extra S hg hf (by omega) hy (by omega)
    omega
  omega

private theorem tip12 (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (hh : g.x=4) (hy : g.y=1) (hk : pair12Count S.D=4)
    (hX : pure1Intercept S=6) (hE : (pair12ExtraFinset S).card=1) :
    MinimalComplement S.D (Point3.mk 5 1 0) := by
  classical
  have hrow : Point3.mk 4 1 0∈S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨by change 4≤g.x;omega,by simp [hy],Nat.zero_le _⟩,
      by intro he;have hez :=congrArg Point3.z he;have :=hf.2.2;change 0=g.z at hez;omega⟩)
  have hrowE : Point3.mk 4 1 0∈pair12ExtraFinset S :=
    (mem_pair12ExtraFinset S _).mpr ⟨hrow,by simp,by simp,rfl,by simp [hk]⟩
  obtain ⟨p,hp⟩:=card_eq_one.mp hE
  have he : Point3.mk 4 1 0=p := by simpa only [hp,mem_singleton] using hrowE
  have hsingle : pair12ExtraFinset S={Point3.mk 4 1 0} := by simpa only [←he] using hp
  refine ⟨?_,?_,?_,by simp⟩
  · intro hd
    have ht : Point3.mk 5 1 0∈pair12ExtraFinset S :=
      (mem_pair12ExtraFinset S _).mpr ⟨hd,by simp,by simp,rfl,by simp [hk]⟩
    rw [hsingle,mem_singleton] at ht
    have :=congrArg Point3.x ht
    norm_num at this
  · intro _;simpa [Point3.pred1] using hrow
  · intro _;simpa [Point3.pred2] using (pure1_axis_mem_iff S 5).mpr (by omega)

private theorem tip13 (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (hh : g.x=4) (hz : g.z=1) (hk : pair13Count S.D=4)
    (hX : pure1Intercept S=6) (hE : (pair13ExtraFinset S).card=1) :
    MinimalComplement S.D (Point3.mk 5 0 1) := by
  classical
  have hrow : Point3.mk 4 0 1∈S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨by change 4≤g.x;omega,Nat.zero_le _,by simp [hz]⟩,
      by intro he;have hey :=congrArg Point3.y he;have :=hf.2.1;change 0=g.y at hey;omega⟩)
  have hrowE : Point3.mk 4 0 1∈pair13ExtraFinset S :=
    (mem_pair13ExtraFinset S _).mpr ⟨hrow,by simp,rfl,by simp,by simp [hk]⟩
  obtain ⟨p,hp⟩:=card_eq_one.mp hE
  have he : Point3.mk 4 0 1=p := by simpa only [hp,mem_singleton] using hrowE
  have hsingle : pair13ExtraFinset S={Point3.mk 4 0 1} := by simpa only [←he] using hp
  refine ⟨?_,?_,by simp,?_⟩
  · intro hd
    have ht : Point3.mk 5 0 1∈pair13ExtraFinset S :=
      (mem_pair13ExtraFinset S _).mpr ⟨hd,by simp,rfl,by simp,by simp [hk]⟩
    rw [hsingle,mem_singleton] at ht
    have :=congrArg Point3.x ht
    norm_num at this
  · intro _;simpa [Point3.pred1] using hrow
  · intro _;simpa [Point3.pred3] using (pure1_axis_mem_iff S 5).mpr (by omega)

/-- The saturated k4 endpoint is impossible without cancelling any weight. -/
theorem t3_balanced_k4_present_no_go (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (he : pair12Count S.D=pair13Count S.D) (hk : pair12Count S.D=4)
    (hh : g.x=4) (hy : g.y=1) (hz : g.z=1)
    (h13 : Point3.mk 0 1 3∈S.D) (h31 : Point3.mk 0 3 1∈S.D)
    (hm : S.m≤42) : False := by
  obtain ⟨hm42,hX,hY,hZ,hE12,hE13,hA⟩:=
    t3_balanced_k4_saturation S hg hf ht he hk hh hy hz h13 h31 hm
  have hzero : S.residue g=0 := by
    have h:=S.residue_rho g
    rw [fullSupport_return_eq_zero S hg hf,CyclicStaircase.residue_zero] at h
    exact h.symm
  have hg0 : 4*S.p1+S.p2+S.p3=0 := by
    simpa [CyclicStaircase.residue,residueOf,hh,hy,hz] using hzero
  have h1 : Point3.e1∈S.D := by
    simpa [Point3.e1] using (pure1_axis_mem_iff S 1).mpr (by omega)
  have hb12:=tip12 S hg hf hh hy hk hX hE12
  have hb13:=tip13 S hg hf hh hz (by omega) hX hE13
  obtain ⟨c,hc⟩:=pair12_return_eq_axis3 S hb12 ⟨by simp,by simp,rfl⟩
  have hcmem:=S.rho_mem (Point3.mk 5 1 0)
  rw [hc] at hcmem
  have hcLt:=(pure3_axis_mem_iff S c).mp hcmem
  have hcres : (c:ZMod S.m)*S.p3=5*S.p1+S.p2 := by
    simpa [hc,CyclicStaircase.residue,residueOf] using S.residue_rho (Point3.mk 5 1 0)
  have hcRel : S.p1=((c+1:ℕ):ZMod S.m)*S.p3 := by
    push_cast at hcres ⊢
    linear_combination -hcres-hg0
  have hcEq : c=4 := by
    by_contra hn
    have heq:=S.standard_eq_of_residue_eq h1
      ((pure3_axis_mem_iff S (c+1)).mpr (by omega))
      (by simpa [CyclicStaircase.residue,residueOf,Point3.e1] using hcRel)
    have hx:=congrArg Point3.x heq
    simp [Point3.e1] at hx
  obtain ⟨d,hd⟩:=pair13_return_eq_axis2 S hb13 ⟨by simp,rfl,by simp⟩
  have hdmem:=S.rho_mem (Point3.mk 5 0 1)
  rw [hd] at hdmem
  have hdLt:=(pure2_axis_mem_iff S d).mp hdmem
  have hdres : (d:ZMod S.m)*S.p2=5*S.p1+S.p3 := by
    simpa [hd,CyclicStaircase.residue,residueOf] using S.residue_rho (Point3.mk 5 0 1)
  have hdRel : S.p1=((d+1:ℕ):ZMod S.m)*S.p2 := by
    push_cast at hdres ⊢
    linear_combination -hdres-hg0
  have hdEq : d=4 := by
    by_contra hn
    have heq:=S.standard_eq_of_residue_eq h1
      ((pure2_axis_mem_iff S (d+1)).mpr (by omega))
      (by simpa [CyclicStaircase.residue,residueOf,Point3.e1] using hdRel)
    have hx:=congrArg Point3.x heq
    simp [Point3.e1] at hx
  rw [hcEq] at hcres
  rw [hdEq] at hdres
  norm_num only [Nat.cast_ofNat] at hcres hdres
  have h22 : (22:ZMod S.m)*S.p1=0 := by
    linear_combination -hcres-hdres+3*hg0
  have h42 : (42:ZMod S.m)=0 :=
    (ZMod.natCast_eq_zero_iff 42 S.m).mpr (by rw [hm42])
  have h2 : (2:ZMod S.m)*S.p1=0 := by
    linear_combination 2*h22-S.p1*h42
  have hmem :=(pure1_axis_mem_iff S 2).mpr (by omega)
  have heq:=S.standard_eq_of_residue_eq hmem S.zero_mem
    (by simpa [CyclicStaircase.residue,residueOf] using h2)
  have hx:=congrArg Point3.x heq
  norm_num at hx

/-- Complete ordered balanced t3/h11 sharp bound, including equal height. -/
theorem fullSupport_t3_balanced_h11_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (he : pair12Count S.D=pair13Count S.D) (hk : 4≤pair12Count S.D)
    (hh : pair12Count S.D≤g.x) (hy : g.y=1) (hz : g.z=1) : fullTarget S≤S.m := by
  classical
  by_cases hstrict : pair12Count S.D<g.x
  · exact fullSupport_t3_balanced_h11_strict_height_sharp S hg hf ho ht he hk hstrict hy hz
  have heq : g.x=pair12Count S.D:=by omega
  by_cases h13 : Point3.mk 0 1 3∈S.D
  · by_cases h31 : Point3.mk 0 3 1∈S.D
    · by_cases hk5 : 5≤pair12Count S.D
      · exact t3_balanced_present_ge5_sharp S hg hf ho ht he hk5 heq hy hz h13 h31
      · by_contra hn
        have hk4 : pair12Count S.D=4:=by omega
        have hm : S.m≤42 := by
          rw [fullTarget_eq_square,←he,hk4,ht] at hn
          norm_num at hn
          omega
        exact t3_balanced_k4_present_no_go S hg hf ho ht he hk4 (by omega) hy hz h13 h31 hm
    · exact t3_balanced_missing_sharp S hg hf ho ht he hk heq hy hz (Or.inr h31)
  · exact t3_balanced_missing_sharp S hg hf ho ht he hk heq hy hz (Or.inl h13)

end NSP3
