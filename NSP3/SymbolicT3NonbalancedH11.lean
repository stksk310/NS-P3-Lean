import NSP3.SymbolicT3Evidence

namespace NSP3
open Finset

/-- Three actual, pairwise disjoint rows in H, including the s=3 endpoint. -/
theorem t3_nonbalanced_h11_H_lower (S : CyclicStaircase) {g : Point3}
    (ht : pair23Count S.D=3) (hs : 3≤pair13Count S.D)
    (hr : pair13Count S.D<pair12Count S.D) (hh : pair12Count S.D≤g.x)
    (hy : g.y=1) (hz : g.z=1) :
    g.x+2*pair13Count S.D-4≤(fullSupportSymbolicH S g).card := by
  classical
  let R0:=(Icc 1 (g.x-1)).image (fun x=>Point3.mk x 1 1)
  let R1:=(Icc 1 (pair13Count S.D-2)).image (fun x=>Point3.mk x 1 2)
  let R2:=(Icc 1 (pair13Count S.D-1)).image (fun x=>Point3.mk x 2 1)
  have h0 : R0⊆fullSupportSymbolicH S g := by
    intro p hp
    obtain ⟨x,hx,rfl⟩:=mem_image.mp hp
    have hx':=mem_Icc.mp hx
    apply mem_union.mpr;right
    refine mem_filter.mpr ⟨(mem_lowerBoxFinset _ _).mpr
      ⟨⟨by change x≤g.x;omega,by simp [hy],by simp [hz]⟩,?_⟩,
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
  have c1 : R1.card=pair13Count S.D-2:=by
    dsimp [R1];rw [card_image_iff.mpr (fun _ _ _ _ heq=>congrArg Point3.x heq)];simp
  have c2 : R2.card=pair13Count S.D-1:=by
    dsimp [R2];rw [card_image_iff.mpr (fun _ _ _ _ heq=>congrArg Point3.x heq)];simp
  have hc:=card_le_card (union_subset (union_subset h0 h1) h2)
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hd02,hd12⟩),
    card_union_of_disjoint hd01,c0,c1,c2] at hc
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
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,ha'.2⟩,
        by simp⟩,by omega⟩
  rw [he,card_image_iff.mpr (fun _ _ _ _ heq=>congrArg Prod.fst heq)]
  simp [Nat.card_Icc]

/-- Source-exact BW budget: axes, three planes and H are charged once. -/
theorem fullSupport_t3_nonbalanced_h11_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : pair13Count S.D<pair12Count S.D) (hh : pair12Count S.D≤g.x)
    (hy : g.y=1) (hz : g.z=1) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      pair12Count S.D+pair13Count S.D+4*g.x+4≤S.m := by
  have hs : 3≤pair13Count S.D:=by have:=ho.1;omega
  have h:=fullSupport_symbolic_BW_lower S hg hf ho
  have hH:=t3_nonbalanced_h11_H_lower S ht hs hr hh hy hz
  have h12 : (ferrersRectangle (pair12Count S.D) g.x 1).card≤
      ferrersPlaneDefect (pair12Count S.D) g.x 1 :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have h13 : (ferrersRectangle (pair13Count S.D) g.x 1).card≤
      ferrersPlaneDefect (pair13Count S.D) g.x 1 :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  rw [row_rectangle _ _ (by omega)] at h12 h13
  have h23 : 2≤ferrersPlaneDefect 3 1 1:=by decide
  unfold fullSupportSymbolicBW at h
  rw [ht,hy,hz] at h
  simp only [max_eq_right hh,max_eq_left (by omega : 1≤pair12Count S.D)] at h
  have hc3 : Nat.choose 3 2=3:=by decide
  rw [hc3] at h
  omega

private theorem nonbalanced_square (r s h : ℕ) (hs : 3 ≤ s) (hr : s < r)
    (hh : r ≤ h) : (r+s+5)^2 ≤ 4*(Nat.choose r 2+Nat.choose s 2+r+s+4*h+4) := by
  have cr : 2*Nat.choose r 2=r*(r-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2=s*(s-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r:=by omega
  have es : s-1+1=s:=by omega
  have ed : r-s+s=r:=Nat.sub_add_cancel (by omega)
  have ha : 1≤r-s:=by omega
  nlinarith only [cr,cs,er,es,ed,hh,ha,Nat.zero_le ((r-s-1)^2)]

/-- All nonbalanced h11 heights above the long count meet the sharp target. -/
theorem fullSupport_t3_nonbalanced_h11_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : pair13Count S.D<pair12Count S.D) (hh : pair12Count S.D≤g.x)
    (hy : g.y=1) (hz : g.z=1) : fullTarget S≤S.m := by
  have hm:=fullSupport_t3_nonbalanced_h11_lower S hg hf ho ht hr hh hy hz
  have hs : 3≤pair13Count S.D:=by have:=ho.1;omega
  have hsq:=nonbalanced_square (pair12Count S.D) (pair13Count S.D) g.x hs hr hh
  have hle : (pair12Count S.D+pair13Count S.D+5)^2≤4*S.m:=by omega
  rw [fullTarget_eq_square,ht]
  norm_num only [Nat.add_assoc] at *
  omega

end NSP3
