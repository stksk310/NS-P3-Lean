import NSP3.SymbolicThin23Endpoint

namespace NSP3
open Finset

private theorem long_row12_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (hr : 0 < pair12Count S.D) (hh : pair12Count S.D ≤ g.x) (hy : g.y=1) :
    g.x-pair12Count S.D+1 ≤ (pair12ExtraFinset S).card := by
  classical
  let f := fun x => Point3.mk x 1 0
  have hsub : (Icc (pair12Count S.D) g.x).image f ⊆ pair12ExtraFinset S := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    have hx' := mem_Icc.mp hx
    apply (mem_pair12ExtraFinset S _).mpr
    refine ⟨lowerBoxFinset_subset_D hg ((mem_lowerBoxFinset _ _).mpr
      ⟨⟨hx'.2,by simp [f,hy],Nat.zero_le _⟩,?_⟩),by dsimp [f]; omega,by simp [f],rfl,?_⟩
    · intro he
      have := congrArg Point3.z he
      have := hf.2.2
      simp [f] at *
      omega
    · dsimp [f]; omega
  have hc := card_le_card hsub
  rw [card_image_iff.mpr (fun _ _ _ _ he => congrArg Point3.x he)] at hc
  simp only [Nat.card_Icc] at hc
  omega

private theorem long_row13_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (hs : 0 < pair13Count S.D) (hh : pair13Count S.D ≤ g.x) (hz : g.z=1) :
    g.x-pair13Count S.D+1 ≤ (pair13ExtraFinset S).card := by
  classical
  let f := fun x => Point3.mk x 0 1
  have hsub : (Icc (pair13Count S.D) g.x).image f ⊆ pair13ExtraFinset S := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    have hx' := mem_Icc.mp hx
    apply (mem_pair13ExtraFinset S _).mpr
    refine ⟨lowerBoxFinset_subset_D hg ((mem_lowerBoxFinset _ _).mpr
      ⟨⟨hx'.2,Nat.zero_le _,by simp [f,hz]⟩,?_⟩),by dsimp [f]; omega,rfl,by simp [f],?_⟩
    · intro he
      have := congrArg Point3.y he
      have := hf.2.1
      simp [f] at *
      omega
    · dsimp [f]; omega
  have hc := card_le_card hsub
  rw [card_image_iff.mpr (fun _ _ _ _ he => congrArg Point3.x he)] at hc
  simp only [Nat.card_Icc] at hc
  omega

private theorem long_face_last_gap (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (hr : 0 < pair12Count S.D) (hy : g.y=1)
    (hX : pure1Intercept S=g.x+1) :
    g.x ≤ (pair12ExtraFinset S).card := by
  classical
  let r := pair12Count S.D
  let b := orderedPair12Boundary S (⟨r-1,by dsimp [r]; omega⟩ : Fin r)
  have hbX := (Ferrers.boundary_lt_intercepts S b).1
  have hrow : Point3.mk g.x 1 0 ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨le_rfl,by simp [hy],Nat.zero_le _⟩,
      by intro he; have hez := congrArg Point3.z he; have := hf.2.2; change 0=g.z at hez; omega⟩)
  have hbY : 2 ≤ b.val.y := by
    have hp := b.property.2.2.1
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
  have hcross : (range (r+1)).sum (Ferrers.gapU S) ≤
      (range (r+1)).sum (fun i =>
        ((range (r+1)).filter (fun j => i ≤ j)).sum
          (fun j => Ferrers.gapU S i*Ferrers.gapV S j)) := by
    apply sum_le_sum
    intro i hi
    have hir : i ≤ r := by have := mem_range.mp hi; omega
    have hmem : r ∈ ((range (r+1)).filter (fun j => i ≤ j)) :=
      mem_filter.mpr ⟨mem_range.mpr (by omega),hir⟩
    have hs := single_le_sum (f := fun j => Ferrers.gapU S i*Ferrers.gapV S j)
      (fun _ _ => Nat.zero_le _) hmem
    have hm := Nat.mul_le_mul_left (Ferrers.gapU S i) hv
    omega
  have hU := Ferrers.gapU_prefix S (k := r+1) le_rfl
  rw [Ferrers.cornerX_last,hX] at hU
  have harea := Ferrers.pair_plane_exact_gap_card S
  have hcard := card_plane12PosFinset S
  change (plane12PosFinset S).card = Nat.choose r 2+
    (range (r+1)).sum (fun i => (r-i)*Ferrers.gapU S i)+
    (range (r+1)).sum (fun j => j*Ferrers.gapV S j)+
    (range (r+1)).sum (fun i => ((range (r+1)).filter (fun j => i ≤ j)).sum
      (fun j => Ferrers.gapU S i*Ferrers.gapV S j)) at harea
  change (plane12PosFinset S).card=Nat.choose r 2+(pair12ExtraFinset S).card at hcard
  omega

private theorem h11_box_card_lower (S : CyclicStaircase) (g : Point3)
    (hy : g.y=1) (hz : g.z=1) : g.x-1 ≤ (fullSupportSymbolicH S g).card := by
  classical
  have hsub : (Icc 1 (g.x-1)).image (fun x => Point3.mk x 1 1) ⊆ fullSupportSymbolicH S g := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    have hx' := mem_Icc.mp hx
    apply mem_union.mpr; right
    apply mem_filter.mpr
    refine ⟨(mem_lowerBoxFinset _ _).mpr ⟨⟨by change x ≤ g.x; omega,by simp [hy],by simp [hz]⟩,?_⟩,
      ⟨hx'.1,by simp,by simp⟩⟩
    intro he
    have := congrArg Point3.x he
    simp only at this
    omega
  have hc := card_le_card hsub
  rw [card_image_iff.mpr (fun _ _ _ _ he => congrArg Point3.x he)] at hc
  simpa using hc


-- Isolated prototype, not part of the frozen249-file release snapshot.
private theorem balanced_saturation (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hr : pair12Count S.D=g.x) (hs : pair13Count S.D=g.x)
    (hk : 3 ≤ g.x) (hy : g.y=1) (hz : g.z=1)
    (hm : S.m=(g.x+1)*(g.x+3)) :
    pure1Intercept S=g.x+2 ∧ pure2Intercept S=g.x+1 ∧ pure3Intercept S=g.x+1 ∧
    (pair12ExtraFinset S).card=1 ∧ (pair13ExtraFinset S).card=1 ∧
    (pair23ExtraFinset S).card=1 := by
  have h12 := long_row12_lower S hg hf
    (by omega) (by omega) hy
  have h13 := long_row13_lower S hg hf
    (by omega) (by omega) hz
  have hH := h11_box_card_lower S g hy hz
  have hC := thin23_lifted_columns_lower S hg hf ho ht (by omega) hy hz
  have hY := pair12_intercept2_lower S
  have hZ := pair12_return_capacity_fullSupport S hg hf
  have h23 := pair23_symbolic_defect_lower S hg hf
  have h23one : 1 ≤ ferrersPlaneDefect (pair23Count S.D) g.y g.z := le_max_left _ _
  have hX : g.x < pure1Intercept S := (pure1_axis_mem_iff S _).mp
    (S.down_closed (b := g.pred2) ⟨le_rfl,Nat.zero_le _,Nat.zero_le _⟩
      (hg.pred2_mem hf.2.1))
  have ha := thin23_disjoint_resource_lower S hg hf
  rw [card_plane12PosFinset,card_plane13PosFinset,card_plane23PosFinset,hr,hs,ht] at ha
  norm_num at ha
  rw [hr] at h12 hY hZ
  rw [hs] at h13 hC
  have hc : 2*Nat.choose g.x 2=g.x*(g.x-1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' g.x.two_dvd_mul_sub_one
  have he : g.x-1+1=g.x := by omega
  have hml : S.m=2*Nat.choose g.x 2+5*g.x+3 := by nlinarith
  have hXne : pure1Intercept S≠g.x+1 := by
    intro hXe
    have hlast := long_face_last_gap
      S hg hf (by omega) hy hXe
    omega
  omega

private theorem balanced_tip12 (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (hk : 3 ≤ g.x)
    (hy : g.y=1) (hr : pair12Count S.D=g.x)
    (hX : pure1Intercept S=g.x+2) (hE : (pair12ExtraFinset S).card=1) :
    MinimalComplement S.D (Point3.mk (g.x+1) 1 0) := by
  classical
  have hrow : Point3.mk g.x 1 0 ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨le_rfl,by simp [hy],Nat.zero_le _⟩,
      by intro he; have hez := congrArg Point3.z he; have := hf.2.2; change 0=g.z at hez; omega⟩)
  have hrowE : Point3.mk g.x 1 0 ∈ pair12ExtraFinset S :=
    (mem_pair12ExtraFinset S _).mpr ⟨hrow,by change 0<g.x; omega,by simp,rfl,by simp [hr]⟩
  obtain ⟨p,hp⟩ := card_eq_one.mp hE
  have he : Point3.mk g.x 1 0=p := by simpa only [hp,mem_singleton] using hrowE
  have hsingle : pair12ExtraFinset S={Point3.mk g.x 1 0} := by simpa only [←he] using hp
  refine ⟨?_,?_,?_,by simp⟩
  · intro hd
    have ht : Point3.mk (g.x+1) 1 0 ∈ pair12ExtraFinset S :=
      (mem_pair12ExtraFinset S _).mpr ⟨hd,by change 0<g.x+1; omega,by simp,rfl,by simp [hr]⟩
    rw [hsingle,mem_singleton] at ht
    have := congrArg Point3.x ht
    simp only at this
    omega
  · intro _; simpa [Point3.pred1] using hrow
  · intro _
    have ha := (pure1_axis_mem_iff S (g.x+1)).mpr (by omega)
    simpa [Point3.pred2] using ha

private theorem balanced_tip13 (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (hk : 3 ≤ g.x)
    (hz : g.z=1) (hs : pair13Count S.D=g.x)
    (hX : pure1Intercept S=g.x+2) (hE : (pair13ExtraFinset S).card=1) :
    MinimalComplement S.D (Point3.mk (g.x+1) 0 1) := by
  classical
  have hrow : Point3.mk g.x 0 1 ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨le_rfl,Nat.zero_le _,by simp [hz]⟩,
      by intro he; have hey := congrArg Point3.y he; have := hf.2.1; change 0=g.y at hey; omega⟩)
  have hrowE : Point3.mk g.x 0 1 ∈ pair13ExtraFinset S :=
    (mem_pair13ExtraFinset S _).mpr ⟨hrow,by change 0<g.x; omega,rfl,by simp,by simp [hs]⟩
  obtain ⟨p,hp⟩ := card_eq_one.mp hE
  have he : Point3.mk g.x 0 1=p := by simpa only [hp,mem_singleton] using hrowE
  have hsingle : pair13ExtraFinset S={Point3.mk g.x 0 1} := by simpa only [←he] using hp
  refine ⟨?_,?_,by simp,?_⟩
  · intro hd
    have ht : Point3.mk (g.x+1) 0 1 ∈ pair13ExtraFinset S :=
      (mem_pair13ExtraFinset S _).mpr ⟨hd,by change 0<g.x+1; omega,rfl,by simp,by simp [hs]⟩
    rw [hsingle,mem_singleton] at ht
    have := congrArg Point3.x ht
    simp only at this
    omega
  · intro _; simpa [Point3.pred1] using hrow
  · intro _
    have ha := (pure1_axis_mem_iff S (g.x+1)).mpr (by omega)
    simpa [Point3.pred3] using ha

private theorem balanced_weights (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (hk : 3 ≤ g.x)
    (hy : g.y=1) (hz : g.z=1)
    (hr : pair12Count S.D=g.x) (hs : pair13Count S.D=g.x)
    (hX : pure1Intercept S=g.x+2) (hY : pure2Intercept S=g.x+1)
    (hZ : pure3Intercept S=g.x+1)
    (hE12 : (pair12ExtraFinset S).card=1) (hE13 : (pair13ExtraFinset S).card=1) :
    S.p1=((g.x+1:ℕ):ZMod S.m)*S.p2 ∧
      S.p1=((g.x+1:ℕ):ZMod S.m)*S.p3 := by
  have hzero : S.residue g=0 := by
    have h := S.residue_rho g
    rw [fullSupport_return_eq_zero S hg hf,CyclicStaircase.residue_zero] at h
    exact h.symm
  have hg0 : (g.x:ZMod S.m)*S.p1+S.p2+S.p3=0 := by
    simpa [CyclicStaircase.residue,residueOf,hy,hz] using hzero
  have h1 : Point3.e1 ∈ S.D := by
    simpa [Point3.e1] using (pure1_axis_mem_iff S 1).mpr (by omega)
  have hb12 := balanced_tip12 S hg hf hk hy hr hX hE12
  have hb13 := balanced_tip13 S hg hf hk hz hs hX hE13
  obtain ⟨c,hc⟩ := pair12_return_eq_axis3 S hb12 ⟨by change 0<g.x+1; omega,by simp,rfl⟩
  have hcmem := S.rho_mem (Point3.mk (g.x+1) 1 0)
  rw [hc] at hcmem
  have hcLt := (pure3_axis_mem_iff S c).mp hcmem
  have hcres : (c:ZMod S.m)*S.p3=((g.x+1:ℕ):ZMod S.m)*S.p1+S.p2 := by
    simpa [hc,CyclicStaircase.residue,residueOf] using S.residue_rho (Point3.mk (g.x+1) 1 0)
  have hcRel : S.p1=((c+1:ℕ):ZMod S.m)*S.p3 := by
    push_cast at hcres ⊢
    linear_combination -hcres-hg0
  have hcEq : c=g.x := by
    by_contra hn
    have hsmall : c+1 < pure3Intercept S := by omega
    have heq := S.standard_eq_of_residue_eq h1 ((pure3_axis_mem_iff S (c+1)).mpr hsmall)
      (by simpa [CyclicStaircase.residue,residueOf,Point3.e1] using hcRel)
    have := congrArg Point3.x heq
    simp [Point3.e1] at this
  obtain ⟨d,hd⟩ := pair13_return_eq_axis2 S hb13 ⟨by change 0<g.x+1; omega,rfl,by simp⟩
  have hdmem := S.rho_mem (Point3.mk (g.x+1) 0 1)
  rw [hd] at hdmem
  have hdLt := (pure2_axis_mem_iff S d).mp hdmem
  have hdres : (d:ZMod S.m)*S.p2=((g.x+1:ℕ):ZMod S.m)*S.p1+S.p3 := by
    simpa [hd,CyclicStaircase.residue,residueOf] using S.residue_rho (Point3.mk (g.x+1) 0 1)
  have hdRel : S.p1=((d+1:ℕ):ZMod S.m)*S.p2 := by
    push_cast at hdres ⊢
    linear_combination -hdres-hg0
  have hdEq : d=g.x := by
    by_contra hn
    have hsmall : d+1 < pure2Intercept S := by omega
    have heq := S.standard_eq_of_residue_eq h1 ((pure2_axis_mem_iff S (d+1)).mpr hsmall)
      (by simpa [CyclicStaircase.residue,residueOf,Point3.e1] using hdRel)
    have := congrArg Point3.x heq
    simp [Point3.e1] at this
  simpa [hcEq,hdEq] using And.intro hdRel hcRel

private theorem balanced_weights_span (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (hk : 3 ≤ g.x)
    (hy : g.y=1) (hz : g.z=1) (ht : pair23Count S.D=2)
    (hY : pure2Intercept S=g.x+1) (hZ : pure3Intercept S=g.x+1)
    (hE : (pair23ExtraFinset S).card=1) :
    ∃ u v : ZMod S.m, S.p2=u*S.p1 ∧ S.p3=v*S.p1 := by
  classical
  have hzero : S.residue g=0 := by
    have h := S.residue_rho g
    rw [fullSupport_return_eq_zero S hg hf,CyclicStaircase.residue_zero] at h
    exact h.symm
  have hg0 : (g.x:ZMod S.m)*S.p1+S.p2+S.p3=0 := by
    simpa [CyclicStaircase.residue,residueOf,hy,hz] using hzero
  have h011 : Point3.mk 0 1 1 ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨Nat.zero_le _,by simp [hy],by simp [hz]⟩,
      by intro he; have hx := congrArg Point3.x he; change 0=g.x at hx; omega⟩)
  rcases thin23_unit_step_base S hg hf ht hy hz with hb | hb
  · have hbE := (mem_filter.mp hb).1
    obtain ⟨p,hp⟩ := card_eq_one.mp hE
    have he : Point3.mk 0 1 2=p := by simpa only [hp,mem_singleton] using hbE
    have hsingle : pair23ExtraFinset S={Point3.mk 0 1 2} := by simpa only [←he] using hp
    have hnot : Point3.mk 0 2 1 ∉ S.D := by
      intro hd
      have htE : Point3.mk 0 2 1 ∈ pair23ExtraFinset S :=
        (mem_pair23ExtraFinset S _).mpr ⟨hd,rfl,by simp,by simp,by simp [ht]⟩
      rw [hsingle,mem_singleton] at htE
      have := congrArg Point3.y htE
      norm_num at this
    have hboundary : MinimalComplement S.D (Point3.mk 0 2 1) := by
      refine ⟨hnot,by simp,?_,?_⟩
      · intro _; simpa [Point3.pred2] using h011
      · intro _
        simpa [Point3.pred3] using (pure2_axis_mem_iff S 2).mpr (by omega)
    obtain ⟨a,ha⟩ := pair23_return_eq_axis1 S hboundary ⟨rfl,by simp,by simp⟩
    have hres : (a:ZMod S.m)*S.p1=2*S.p2+S.p3 := by
      simpa [ha,CyclicStaircase.residue,residueOf] using S.residue_rho (Point3.mk 0 2 1)
    have hp2 : S.p2=((g.x:ZMod S.m)+(a:ZMod S.m))*S.p1 := by
      linear_combination -hres-hg0
    refine ⟨(g.x:ZMod S.m)+(a:ZMod S.m),
      -(g.x:ZMod S.m)-((g.x:ZMod S.m)+(a:ZMod S.m)),hp2,?_⟩
    rw [hp2] at hg0
    linear_combination hg0
  · have hbE := (mem_filter.mp hb).1
    obtain ⟨p,hp⟩ := card_eq_one.mp hE
    have he : Point3.mk 0 2 1=p := by simpa only [hp,mem_singleton] using hbE
    have hsingle : pair23ExtraFinset S={Point3.mk 0 2 1} := by simpa only [←he] using hp
    have hnot : Point3.mk 0 1 2 ∉ S.D := by
      intro hd
      have htE : Point3.mk 0 1 2 ∈ pair23ExtraFinset S :=
        (mem_pair23ExtraFinset S _).mpr ⟨hd,rfl,by simp,by simp,by simp [ht]⟩
      rw [hsingle,mem_singleton] at htE
      have := congrArg Point3.y htE
      norm_num at this
    have hboundary : MinimalComplement S.D (Point3.mk 0 1 2) := by
      refine ⟨hnot,by simp,?_,?_⟩
      · intro _
        simpa [Point3.pred2] using (pure3_axis_mem_iff S 2).mpr (by omega)
      · intro _; simpa [Point3.pred3] using h011
    obtain ⟨a,ha⟩ := pair23_return_eq_axis1 S hboundary ⟨rfl,by simp,by simp⟩
    have hres : (a:ZMod S.m)*S.p1=S.p2+2*S.p3 := by
      simpa [ha,CyclicStaircase.residue,residueOf] using S.residue_rho (Point3.mk 0 1 2)
    have hp3 : S.p3=((g.x:ZMod S.m)+(a:ZMod S.m))*S.p1 := by
      linear_combination -hres-hg0
    refine ⟨-(g.x:ZMod S.m)-((g.x:ZMod S.m)+(a:ZMod S.m)),
      (g.x:ZMod S.m)+(a:ZMod S.m),?_,hp3⟩
    rw [hp3] at hg0
    linear_combination hg0

theorem fullSupport_t2_h11_balanced_equality_impossible
    (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hr : pair12Count S.D=g.x) (hs : pair13Count S.D=g.x)
    (hk : 3 ≤ g.x) (hy : g.y=1) (hz : g.z=1)
    (hm : S.m=(g.x+1)*(g.x+3)) : False := by
  obtain ⟨hX,hY,hZ,h12,h13,h23⟩ := balanced_saturation S hg hf ho ht hr hs hk hy hz hm
  obtain ⟨hw2,hw3⟩ := balanced_weights S hg hf hk hy hz hr hs hX hY hZ h12 h13
  obtain ⟨u,v,hp2,hp3⟩ := balanced_weights_span S hg hf hk hy hz ht hY hZ h23
  have hzero : S.residue g=0 := by
    have h := S.residue_rho g
    rw [fullSupport_return_eq_zero S hg hf,CyclicStaircase.residue_zero] at h
    exact h.symm
  have hg0 : (g.x:ZMod S.m)*S.p1+S.p2+S.p3=0 := by
    simpa [CyclicStaircase.residue,residueOf,hy,hz] using hzero
  have hann : ((g.x*g.x+g.x+2:ℕ):ZMod S.m)*S.p1=0 := by
    push_cast at hw2 hw3 ⊢
    linear_combination ((g.x:ZMod S.m)+1)*hg0+hw2+hw3
  let q := S.residueEquiv.symm (1:ZMod S.m)
  have hq : S.residue q.val=1 := by
    calc
      S.residue q.val=S.residueEquiv q := (S.residueEquiv_spec q).symm
      _=1 := S.residueEquiv.apply_symm_apply _
  let a : ZMod S.m := (q.val.x:ZMod S.m)+(q.val.y:ZMod S.m)*u+(q.val.z:ZMod S.m)*v
  have ha : a*S.p1=1 := by
    calc
      a*S.p1=S.residue q.val := by
        dsimp [a,CyclicStaircase.residue,residueOf]
        rw [hp2,hp3]
        ring
      _=1 := hq
  have hNzero : ((g.x*g.x+g.x+2:ℕ):ZMod S.m)=0 := by
    calc
      ((g.x*g.x+g.x+2:ℕ):ZMod S.m)=
          ((g.x*g.x+g.x+2:ℕ):ZMod S.m)*(a*S.p1) := by rw [ha,mul_one]
      _=a*(((g.x*g.x+g.x+2:ℕ):ZMod S.m)*S.p1) := by ring
      _=0 := by rw [hann,mul_zero]
  have hdvd := (ZMod.natCast_eq_zero_iff (g.x*g.x+g.x+2) S.m).mp hNzero
  have hpos : 0<g.x*g.x+g.x+2 := by omega
  have hle := Nat.le_of_dvd hpos hdvd
  nlinarith

theorem fullSupport_t2_h11_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hs : 2 ≤ pair13Count S.D) (hy : g.y=1) (hz : g.z=1) :
    fullTarget S ≤ S.m := by
  by_contra hn
  have hfail : S.m<fullTarget S := by omega
  obtain ⟨hr,hsEq,hk,hm⟩ := thin23_failure_forces_balanced_equality S hg hf ho ht hs hy hz hfail
  exact fullSupport_t2_h11_balanced_equality_impossible S hg hf ho ht hr hsEq hk hy hz hm








end NSP3
