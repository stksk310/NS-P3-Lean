import NSP3.SymbolicThin23Lower

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

/-- The extra unit is a single joint payment by the x axis and xy face. -/
theorem long_face_axis_joint_unit (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (hr : 2 ≤ pair12Count S.D) (hh : pair12Count S.D ≤ g.x) (hy : g.y=1) :
    1 ≤ (pure1Intercept S-1-g.x)+
      ((pair12ExtraFinset S).card-(g.x-pair12Count S.D+1)) := by
  have hrow := long_row12_lower S hg hf (by omega) hh hy
  have hx : g.x < pure1Intercept S := (pure1_axis_mem_iff S _).mp
    (S.down_closed (b := g.pred2) ⟨le_rfl,Nat.zero_le _,Nat.zero_le _⟩
      (hg.pred2_mem hf.2.1))
  by_cases hX : pure1Intercept S=g.x+1
  · have hface := long_face_last_gap S hg hf (by omega) hy hX
    omega
  · omega

/-- Exact support partition: origin/axes/three positive faces/full support.
    Arbitrary actual full-support resources may be substituted without overlap. -/
theorem support_resources_card_lower (S : CyclicStaircase) (F : Finset Point3)
    (hD : F ⊆ S.D) (hF : ∀ p ∈ F, FullSupport p) :
    pure1Intercept S+pure2Intercept S+pure3Intercept S-2+
      (plane12PosFinset S).card+(plane13PosFinset S).card+
      (plane23PosFinset S).card+F.card ≤ S.m := by
  classical
  let Q := S.D.filter (fun p => p.z≠0)
  let R := Q.filter (fun p => p.y=0)
  let T := Q.filter (fun p => p.y≠0)
  have h0 := card_filter_add_card_filter_not (s := S.D) (fun p => p.z=0)
  have h1 := card_filter_add_card_filter_not (s := Q) (fun p => p.y=0)
  have h2 := card_filter_add_card_filter_not (s := R) (fun p => p.x=0)
  have h3 := card_filter_add_card_filter_not (s := T) (fun p => p.x=0)
  have hP0 : S.D.filter (fun p => p.z=0)=pair12PlaneSection S.D := rfl
  have hP13 : R.filter (fun p => ¬ p.x=0)=plane13PosFinset S := by
    ext p; simp only [R,Q,mem_filter,mem_plane13PosFinset]
    constructor
    · rintro ⟨⟨⟨hd,hz⟩,hy⟩,hx⟩; exact ⟨hd,by omega,hy,by omega⟩
    · rintro ⟨hd,hx,hy,hz⟩; exact ⟨⟨⟨hd,by omega⟩,hy⟩,by omega⟩
  have hP23 : T.filter (fun p => p.x=0)=plane23PosFinset S := by
    ext p; simp only [T,Q,mem_filter,mem_plane23PosFinset]
    constructor
    · rintro ⟨⟨⟨hd,hz⟩,hy⟩,hx⟩; exact ⟨hd,hx,by omega,by omega⟩
    · rintro ⟨hd,hx,hy,hz⟩; exact ⟨⟨⟨hd,by omega⟩,by omega⟩,hx⟩
  have hfull : F ⊆ T.filter (fun p => ¬ p.x=0) := by
    intro p hp
    have hf := hF p hp
    simp only [T,Q,mem_filter]
    exact ⟨⟨⟨hD hp,by have := hf.2.2; omega⟩,by have := hf.2.1; omega⟩,
      by have := hf.1; omega⟩
  have haxis : R.filter (fun p => p.x=0)=
      (Ico 1 (pure3Intercept S)).image (fun z => Point3.mk 0 0 z) := by
    ext p
    simp only [R,Q,mem_filter,mem_image,mem_Ico]
    constructor
    · rintro ⟨⟨⟨hd,hz⟩,hy⟩,hx⟩
      have he : Point3.mk 0 0 p.z=p := by ext <;> simp [hx,hy]
      exact ⟨p.z,⟨by omega,(pure3_axis_mem_iff S _).mp (he ▸ hd)⟩,he⟩
    · rintro ⟨z,⟨hz,hZ⟩,rfl⟩
      exact ⟨⟨⟨(pure3_axis_mem_iff S _).mpr hZ,by simpa using (show z≠0 by omega)⟩,rfl⟩,rfl⟩
  have haxisCard : (R.filter (fun p => p.x=0)).card=pure3Intercept S-1 := by
    rw [haxis,card_image_iff.mpr (fun _ _ _ _ he => congrArg Point3.z he)]
    simp
  rw [hP0] at h0
  rw [hP13,haxisCard] at h2
  rw [hP23] at h3
  have hc := card_le_card hfull
  have haxes := Ferrers.pair12_remove_axes S
  have hz : 0 < pure3Intercept S := by simpa using (pure3Intercept_pure S).2.2
  have hx : 0 < pure1Intercept S := by simpa using (pure1Intercept_pure S).1
  have hy : 0 < pure2Intercept S := by simpa using (pure2Intercept_pure S).2.1
  rw [S.card_D] at h0
  change (pair12PlaneSection S.D).card+Q.card=S.m at h0
  change R.card+T.card=Q.card at h1
  omega

/-- Full-support resources H and the new columns are disjoint before counting. -/
theorem thin23_disjoint_resource_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    pure1Intercept S+pure2Intercept S+pure3Intercept S-2+
      (plane12PosFinset S).card+(plane13PosFinset S).card+
      (plane23PosFinset S).card+(fullSupportSymbolicH S g).card+
      (thin23LiftedColumns S g).card ≤ S.m := by
  classical
  have hH : fullSupportSymbolicH S g ⊆ S.D := by
    intro p hp
    rcases mem_union.mp hp with hc | hb
    · exact puncturedFullCoreFinset_subset_D S hg hf hc
    · exact lowerBoxFinset_subset_D hg (mem_filter.mp hb).1
  have hHF : ∀ p ∈ fullSupportSymbolicH S g, FullSupport p := by
    intro p hp
    rcases mem_union.mp hp with hc | hb
    · exact fullSupport_of_mem_puncturedFullCoreFinset hc
    · exact (mem_filter.mp hb).2
  have h := support_resources_card_lower S
    (fullSupportSymbolicH S g ∪ thin23LiftedColumns S g)
    (union_subset hH (thin23_lifted_columns_subset_D S hg hf)) (by
      intro p hp
      rcases mem_union.mp hp with hp | hp
      · exact hHF p hp
      · exact thin23_lifted_columns_fullSupport S g hp)
  rw [card_union_of_disjoint (thin23_lifted_columns_disjoint_H S g).symm] at h
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

/-- General t=2 h11 resource lower bound, without finite census premises. -/
theorem fullSupport_t2_h11_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hs : 2 ≤ pair13Count S.D) (hy : g.y=1) (hz : g.z=1) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      4*g.x+pair12Count S.D+3 ≤ S.m := by
  have hcap := pair12_terminal_return_capacity_ordered S hg hf ho
  have hrs := ho.2
  have hh : pair12Count S.D ≤ g.x := by omega
  have h12 := long_row12_lower S hg hf (by omega) hh hy
  have h13 := long_row13_lower S hg hf (by omega) (by omega) hz
  have hj := long_face_axis_joint_unit S hg hf (by omega) hh hy
  have hx : g.x < pure1Intercept S := (pure1_axis_mem_iff S _).mp
    (S.down_closed (b := g.pred2) ⟨le_rfl,Nat.zero_le _,Nat.zero_le _⟩
      (hg.pred2_mem hf.2.1))
  have hY := pair12_intercept2_lower S
  have hZ := pair12_return_capacity_fullSupport S hg hf
  have h23 := pair23_symbolic_defect_lower S hg hf
  have h23one : 1 ≤ ferrersPlaneDefect (pair23Count S.D) g.y g.z := le_max_left _ _
  have hb := h11_box_card_lower S g hy hz
  have hl := thin23_lifted_columns_lower S hg hf ho ht hs hy hz
  have ha := thin23_disjoint_resource_lower S hg hf
  rw [card_plane12PosFinset,card_plane13PosFinset,card_plane23PosFinset,ht] at ha
  norm_num at ha
  omega

end NSP3
