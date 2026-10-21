import NSP3.SymbolicT2Sharp

namespace NSP3
open Finset

/-- Three actual high corners require two strict internal gaps. -/
theorem thin23_three_corner_area_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hz : g.z=1) :
    5≤(plane23PosFinset S).card := by
  have hdef:=pair23_symbolic_defect_lower S hg hf
  have hd : 2≤ferrersPlaneDefect 3 1 1:=by decide
  rw [ht,hy,hz] at hdef
  have hc:=card_plane23PosFinset S
  rw [ht] at hc
  norm_num at hc
  omega

/-- Equality in the three-corner area bound forces the universal minimal shape
    (1,4),(2,2),(4,1); the pure-axis endpoint gaps remain unconstrained. -/
theorem thin23_three_corner_minimal_shape (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hz : g.z=1)
    (he : (plane23PosFinset S).card=5) :
    Ferrers23.cornerX S 1=1 ∧ Ferrers23.cornerY S 1=4 ∧
    Ferrers23.cornerX S 2=2 ∧ Ferrers23.cornerY S 2=2 ∧
    Ferrers23.cornerX S 3=4 ∧ Ferrers23.cornerY S 3=1 := by
  have h1:=Ferrers23.high_edge_gap S hg hf (i:=1) (by simp [hy,hz,ht])
  have h2:=Ferrers23.high_edge_gap S hg hf (i:=2) (by simp [hy,hz,ht])
  rw [hy,hz] at h1 h2
  have ha:=Ferrers23.pair_plane_exact_gap_card S
  rw [ht,he] at ha
  norm_num [sum_range_succ,sum_filter] at ha
  have hu0 : Ferrers23.gapU S 0=0:=by omega
  have hu1 : Ferrers23.gapU S 1=0:=by omega
  have hu2 : Ferrers23.gapU S 2=1:=by omega
  have hv1 : Ferrers23.gapV S 1=1:=by omega
  have hv2 : Ferrers23.gapV S 2=0:=by omega
  have hv3 : Ferrers23.gapV S 3=0:=by omega
  have hx1:=Ferrers23.gapU_prefix S (k:=1) (by omega)
  have hx2:=Ferrers23.gapU_prefix S (k:=2) (by omega)
  have hx3:=Ferrers23.gapU_prefix S (k:=3) (by omega)
  have hy1:=Ferrers23.gapV_prefix S (k:=1) (by omega)
  have hy2:=Ferrers23.gapV_prefix S (k:=2) (by omega)
  have hy3:=Ferrers23.gapV_prefix S (k:=3) (by omega)
  have hy4:=Ferrers23.gapV_prefix S (k:=4) (by omega)
  have hlast : Ferrers23.cornerY S 4=0:=by simpa only [ht] using Ferrers23.cornerY_last S
  rw [hlast] at hy4
  norm_num [sum_range_succ] at hx1 hx2 hx3 hy1 hy2 hy3 hy4
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

private theorem h11_three_rows (S : CyclicStaircase) {g : Point3}
    (ht : pair23Count S.D=3) (he : pair12Count S.D=pair13Count S.D)
    (hk : 4≤pair12Count S.D) (hh : pair12Count S.D≤g.x) (hy : g.y=1) (hz : g.z=1) :
    g.x+2*pair12Count S.D-5≤(fullSupportSymbolicH S g).card := by
  classical
  let R0:=(Icc 1 (g.x-1)).image (fun x=>Point3.mk x 1 1)
  let R1:=(Icc 1 (pair12Count S.D-2)).image (fun x=>Point3.mk x 1 2)
  let R2:=(Icc 1 (pair12Count S.D-2)).image (fun x=>Point3.mk x 2 1)
  have h0 : R0⊆fullSupportSymbolicH S g := by
    intro p hp
    obtain ⟨x,hx,rfl⟩:=mem_image.mp hp
    have hx':=mem_Icc.mp hx
    apply mem_union.mpr;right
    refine mem_filter.mpr ⟨(mem_lowerBoxFinset _ _).mpr ⟨⟨by change x≤g.x;omega,by simp [hy],by simp [hz]⟩,?_⟩,
      by simp [FullSupport];omega⟩
    intro heq
    have :=congrArg Point3.x heq
    change x=g.x at this
    omega
  have h1 : R1⊆fullSupportSymbolicH S g := by
    intro p hp
    obtain ⟨x,hx,rfl⟩:=mem_image.mp hp
    have hx':=mem_Icc.mp hx
    apply mem_union.mpr;left
    apply (mem_puncturedFullCoreFinset _ _ _).mpr
    refine ⟨?_,?_⟩
    · simp only [FullCore]
      exact ⟨by omega,by decide,by decide,by omega,by omega,by omega⟩
    · intro hle
      have :=hle.1;change g.x≤x at this;omega
  have h2 : R2⊆fullSupportSymbolicH S g := by
    intro p hp
    obtain ⟨x,hx,rfl⟩:=mem_image.mp hp
    have hx':=mem_Icc.mp hx
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
  have c0 : R0.card=g.x-1:=by
    dsimp [R0];rw [card_image_iff.mpr (fun _ _ _ _ heq=>congrArg Point3.x heq)];simp
  have c1 : R1.card=pair12Count S.D-2:=by
    dsimp [R1];rw [card_image_iff.mpr (fun _ _ _ _ heq=>congrArg Point3.x heq)];simp
  have c2 : R2.card=pair12Count S.D-2:=by
    dsimp [R2];rw [card_image_iff.mpr (fun _ _ _ _ heq=>congrArg Point3.x heq)];simp
  have hc:=card_le_card (union_subset (union_subset h0 h1) h2)
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hd02,hd12⟩),card_union_of_disjoint hd01,c0,c1,c2] at hc
  omega

private theorem row_rectangle (n A : ℕ) (hn : 1≤n) :
    (ferrersRectangle n A 1).card=A+1-n := by
  classical
  have he : ferrersRectangle n A 1=(Icc n A).image (fun a=>(a,1)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hprod,hs⟩:=mem_filter.mp hp
      obtain ⟨ha,hb⟩:=mem_product.mp hprod
      have ha':=mem_Icc.mp ha
      have hb':=mem_Icc.mp hb
      exact mem_image.mpr ⟨p.1,mem_Icc.mpr ⟨by omega,ha'.2⟩,Prod.ext rfl (by omega)⟩
    · intro hp
      obtain ⟨a,ha,rfl⟩:=mem_image.mp hp
      have ha':=mem_Icc.mp ha
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,ha'.2⟩,by simp⟩,by omega⟩
  rw [he,card_image_iff.mpr (fun _ _ _ _ heq=>congrArg Prod.fst heq)]
  simp [Nat.card_Icc]

/-- The general balanced h11 baseline counts three disjoint full-support rows. -/
theorem fullSupport_t3_balanced_h11_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (he : pair12Count S.D=pair13Count S.D) (hk : 4≤pair12Count S.D)
    (hh : pair12Count S.D≤g.x) (hy : g.y=1) (hz : g.z=1) :
    (pair12Count S.D)^2+pair12Count S.D+4*g.x+3≤S.m := by
  have h:=fullSupport_symbolic_BW_lower S hg hf ho
  have hH:=h11_three_rows S ht he hk hh hy hz
  have h12 : (ferrersRectangle (pair12Count S.D) g.x 1).card≤ferrersPlaneDefect (pair12Count S.D) g.x 1 :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have h13 : (ferrersRectangle (pair12Count S.D) g.x 1).card≤ferrersPlaneDefect (pair12Count S.D) g.x 1 :=h12
  rw [row_rectangle _ _ (by omega)] at h12 h13
  have h23 : 2≤ferrersPlaneDefect 3 1 1:=by decide
  unfold fullSupportSymbolicBW at h
  rw [←he,ht,hy,hz] at h
  simp only [max_eq_right hh,max_eq_left (by omega : 1≤pair12Count S.D)] at h
  norm_num only [Nat.choose_succ_self,Nat.choose_two_right] at h
  have cr : 2*Nat.choose (pair12Count S.D) 2=pair12Count S.D*(pair12Count S.D-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' (pair12Count S.D).two_dvd_mul_sub_one
  have hbase : 2*Nat.choose (pair12Count S.D) 2+2*pair12Count S.D+4*g.x+3≤S.m := by
    rw [Nat.choose_two_right]
    omega
  have er : pair12Count S.D-1+1=pair12Count S.D:=by omega
  nlinarith only [hbase,cr,er]

/-- All balanced t3/h11 heights strictly above k already meet the sharp target. -/
theorem fullSupport_t3_balanced_h11_strict_height_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (he : pair12Count S.D=pair13Count S.D) (hk : 4≤pair12Count S.D)
    (hh : pair12Count S.D<g.x) (hy : g.y=1) (hz : g.z=1) : fullTarget S≤S.m := by
  have hm:=fullSupport_t3_balanced_h11_lower S hg hf ho ht he hk (by omega) hy hz
  have hsq : (pair12Count S.D+pair12Count S.D+5)^2≤4*S.m := by
    nlinarith only [hm,hh]
  rw [fullTarget_eq_square,←he,ht]
  norm_num only [Nat.add_assoc] at *
  omega

end NSP3
