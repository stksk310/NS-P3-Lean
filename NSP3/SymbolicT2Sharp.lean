import NSP3.SymbolicT2OneUnit

namespace NSP3
open Finset

private theorem rectangle_unit_right (n A : ℕ) (hn : 1≤n) :
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
  rw [he,card_image_iff.mpr (fun _ _ _ _ he=>congrArg Prod.fst he)]
  simp [Nat.card_Icc]

private theorem rectangle_unit_left (n A : ℕ) (hn : 1≤n) :
    (ferrersRectangle n 1 A).card=A+1-n := by
  classical
  have he : ferrersRectangle n 1 A=(Icc n A).image (fun a=>(1,a)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hprod,hs⟩:=mem_filter.mp hp
      obtain ⟨ha,hb⟩:=mem_product.mp hprod
      have ha':=mem_Icc.mp ha
      have hb':=mem_Icc.mp hb
      exact mem_image.mpr ⟨p.2,mem_Icc.mpr ⟨by omega,hb'.2⟩,Prod.ext (by omega) rfl⟩
    · intro hp
      obtain ⟨a,ha,rfl⟩:=mem_image.mp hp
      have ha':=mem_Icc.mp ha
      exact mem_filter.mpr ⟨mem_product.mpr ⟨by simp,mem_Icc.mpr ⟨by omega,ha'.2⟩⟩,by omega⟩
  rw [he,card_image_iff.mpr (fun _ _ _ _ he=>congrArg Prod.snd he)]
  simp [Nat.card_Icc]

private theorem W11_positive (n : ℕ) (hn : 2≤n) : 1≤ferrersW n 1 1 := by
  have hm : 1∈Icc 1 (n-1):=mem_Icc.mpr ⟨le_rfl,by omega⟩
  have hs:=single_le_sum (f:=fun i=>min (1*(n-i)) (1*i))
    (fun _ _=>Nat.zero_le _) hm
  unfold ferrersW
  simpa only [one_mul,Nat.min_eq_right (by omega : 1≤n-1)] using hs

private theorem W11_three (n : ℕ) (hn : 4≤n) : 3≤ferrersW n 1 1 := by
  have hsub : ({1,2} : Finset ℕ)⊆Icc 1 (n-1) := by
    intro i hi
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact mem_Icc.mpr ⟨by omega,by omega⟩
  have hs:=sum_le_sum_of_subset_of_nonneg (f:=fun i=>min (1*(n-i)) (1*i))
    hsub (by intros;exact Nat.zero_le _)
  simp only [sum_insert (by decide : (1:ℕ)∉({2}:Finset ℕ)),sum_singleton,one_mul] at hs
  unfold ferrersW
  simp only [one_mul]
  omega

/-- One actual H-point beyond the positive box adds a genuine disjoint unit. -/
private theorem positive_box_extra (S : CyclicStaircase) (g p : Point3)
    (hf : FullSupport g) (hp : p∈fullSupportSymbolicH S g) (hout : g.x<p.x) :
    g.x*g.y*g.z≤(fullSupportSymbolicH S g).card := by
  classical
  let P:=(Icc 1 g.x).product ((Icc 1 g.y).product (Icc 1 g.z))
  let f : ℕ×(ℕ×ℕ)→Point3:=fun a=>⟨a.1,a.2.1,a.2.2⟩
  have hi : Set.InjOn f P := by
    intro a _ b _ he
    exact Prod.ext (congrArg Point3.x he) (Prod.ext (congrArg Point3.y he) (congrArg Point3.z he))
  have hc : (P.image f).card=g.x*g.y*g.z:=by rw [card_image_of_injOn hi];simp [P,Nat.mul_assoc]
  have hm : g∈P.image f := by
    have hx:=hf.1;have hy:=hf.2.1;have hz:=hf.2.2
    exact mem_image.mpr ⟨(g.x,(g.y,g.z)),by simp [P];omega,rfl⟩
  have hsub : (P.image f).erase g⊆fullSupportSymbolicH S g := by
    intro q hq
    obtain ⟨hne,hq⟩:=mem_erase.mp hq
    obtain ⟨a,ha,rfl⟩:=mem_image.mp hq
    obtain ⟨hxl,hxu,hyl,hyu,hzl,hzu⟩:=(show 1≤a.1∧a.1≤g.x∧1≤a.2.1∧a.2.1≤g.y∧1≤a.2.2∧a.2.2≤g.z by
      simpa [P,mem_product,mem_Icc,and_assoc] using ha)
    apply mem_union.mpr;right
    exact mem_filter.mpr ⟨(mem_lowerBoxFinset _ _).mpr ⟨⟨hxu,hyu,hzu⟩,hne⟩,⟨hxl,hyl,hzl⟩⟩
  have hnot : p∉(P.image f).erase g := by
    intro hmem
    obtain ⟨a,ha,he⟩:=mem_image.mp (mem_of_mem_erase hmem)
    have hx : a.1≤g.x:= (mem_Icc.mp (mem_product.mp ha).1).2
    have hpx:=congrArg Point3.x he
    change a.1=p.x at hpx
    omega
  have h:=card_le_card (insert_subset hp hsub)
  rw [card_insert_of_notMem hnot,card_erase_of_mem hm,hc] at h
  have hpos:=Nat.mul_pos (Nat.mul_pos hf.1 hf.2.1) hf.2.2
  omega

private theorem core211_extra (S : CyclicStaircase) {g : Point3}
    (hf : FullSupport g) (hx : g.x=1)
    (hr : pair12Count S.D=3) (hs : pair13Count S.D=3) (ht : pair23Count S.D=2)
    (hp : (g.y=1 ∧ 3≤g.z) ∨ (g.z=1 ∧ 3≤g.y)) :
    g.x*g.y*g.z≤(fullSupportSymbolicH S g).card := by
  have hmem : Point3.mk 2 1 1∈fullSupportSymbolicH S g := by
    apply mem_union.mpr;left
    apply (mem_puncturedFullCoreFinset _ _ _).mpr
    refine ⟨by norm_num [FullCore,hr,hs,ht],?_⟩
    intro hle
    rcases hp with ⟨_,hz⟩ | ⟨_,hy⟩
    · have := hle.2.2;change g.z≤1 at this;omega
    · have := hle.2.1;change g.y≤1 at this;omega
  exact positive_box_extra S g _ hf hmem (by simp [hx])

private theorem two_unit_arithmetic (r s W K : ℕ) (hr : 3 ≤ r) (hs : 2 ≤ s)
    (ho : s ≤ r) (hW : 1 ≤ W) (hW4 : r = s → 4 ≤ r → 3 ≤ W)
    (hW3 : r = s → r = 3 → 2 ≤ W ∧ 1 ≤ K) :
    ((r+s+4)^2+3)/4≤1+5*r+Nat.choose r 2+Nat.choose s 2+W+K := by
  have cr : 2*Nat.choose r 2=r*(r-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2=s*(s-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r:=by omega
  have es : s-1+1=s:=by omega
  have ed : r-s+s=r:=Nat.sub_add_cancel ho
  have hsq : (r+s+4)^2≤4*(1+5*r+Nat.choose r 2+Nat.choose s 2+W+K) := by
    by_cases he : r=s
    · by_cases hr4 : 4≤r
      · have hw:=hW4 he hr4
        nlinarith only [cr,cs,er,es,he,hw,Nat.zero_le K]
      · have he3 : r=3:=by omega
        obtain ⟨hw,hk⟩:=hW3 he he3
        nlinarith only [cr,cs,er,es,he,hw,hk]
    · have ha : 1≤r-s:=by omega
      nlinarith only [cr,cs,er,es,ed,ha,hW,Nat.zero_le K,Nat.zero_le ((r-s)^2)]
  omega

/-- Two transverse units use terminal capacity, actual rectangles, and one extra
    disjoint core resource at the balanced332 endpoint. -/
theorem fullSupport_t2_two_transverse_units_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hx : g.x=1) (hp : g.y=1 ∨ g.z=1) : fullTarget S≤S.m := by
  classical
  have hs : 2≤pair13Count S.D:=by have:=ho.1;omega
  have hrs:=ho.2
  by_cases hr : 3≤pair12Count S.D
  · let K : ℕ:=if pair12Count S.D=pair13Count S.D ∧ pair12Count S.D=3 then 1 else 0
    have hcap:=pair12_terminal_return_capacity_ordered S hg hf ho
    have hH:=positive_box_H_lower S g hf
    have h:=fullSupport_symbolic_BW_lower S hg hf ho
    have hD12 : (ferrersRectangle (pair12Count S.D) g.x g.y).card≤ferrersPlaneDefect (pair12Count S.D) g.x g.y :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hD13 : (ferrersRectangle (pair13Count S.D) g.x g.z).card≤ferrersPlaneDefect (pair13Count S.D) g.x g.z :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hD23 : (ferrersRectangle 2 g.y g.z).card≤ferrersPlaneDefect 2 g.y g.z :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hW12 : ferrersW (pair12Count S.D) g.x g.y≤ferrersPlaneDefect (pair12Count S.D) g.x g.y :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hW13 : ferrersW (pair13Count S.D) g.x g.z≤ferrersPlaneDefect (pair13Count S.D) g.x g.z :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    unfold fullSupportSymbolicBW at h
    rw [ht,hx] at h
    rw [hx] at hH hD12 hD13 hW12 hW13 hcap
    rcases hp with hy | hz
    · have hlong : pair12Count S.D≤g.z:=by omega
      have hHK : g.z-1+K≤(fullSupportSymbolicH S g).card := by
        by_cases he : pair12Count S.D=pair13Count S.D ∧ pair12Count S.D=3
        · have hex:=core211_extra S hf hx he.2 (by omega) ht (Or.inl ⟨hy,by omega⟩)
          simp only [hx,hy,one_mul] at hex
          simp only [K,if_pos he]
          omega
        · simp only [K,if_neg he]
          simpa only [hx,hy,one_mul,Nat.add_zero] using hH
      rw [hy] at h hD12 hD23 hW12
      rw [rectangle_unit_left _ _ (by omega)] at hD13
      rw [rectangle_unit_left _ _ (by omega)] at hD23
      have ha:=two_unit_arithmetic (pair12Count S.D) (pair13Count S.D)
        (ferrersW (pair12Count S.D) 1 1) K hr hs ho.2 (W11_positive _ (by omega))
        (by intro _ hr4;exact W11_three _ hr4) (by
          intro he he3
          constructor
          · rw [he3];decide
          · have hs3 : pair13Count S.D=3:=by omega
            simp [K,he3,hs3])
      have hb : 1+5*pair12Count S.D+Nat.choose (pair12Count S.D) 2+
          Nat.choose (pair13Count S.D) 2+ferrersW (pair12Count S.D) 1 1+K≤S.m := by
        simp only [max_eq_left (by omega : 1≤pair12Count S.D),max_eq_right hlong] at h
        norm_num only [Nat.choose_self] at h
        omega
      rw [fullTarget_eq_square,ht]
      exact le_trans (by simpa only [Nat.add_assoc] using ha) hb
    · have hlong : pair12Count S.D≤g.y:=by omega
      have hHK : g.y-1+K≤(fullSupportSymbolicH S g).card := by
        by_cases he : pair12Count S.D=pair13Count S.D ∧ pair12Count S.D=3
        · have hex:=core211_extra S hf hx he.2 (by omega) ht (Or.inr ⟨hz,by omega⟩)
          simp only [hx,hz,one_mul,mul_one] at hex
          simp only [K,if_pos he]
          omega
        · simp only [K,if_neg he]
          simpa only [hx,hz,one_mul,mul_one,Nat.add_zero] using hH
      rw [hz] at h hD13 hD23 hW13
      rw [rectangle_unit_left _ _ (by omega)] at hD12
      rw [rectangle_unit_right _ _ (by omega)] at hD23
      have ha:=two_unit_arithmetic (pair12Count S.D) (pair13Count S.D)
        (ferrersW (pair13Count S.D) 1 1) K hr hs ho.2 (W11_positive _ hs)
        (by intro he hr4;exact W11_three _ (by omega)) (by
          intro he he3
          constructor
          · have hs3 : pair13Count S.D=3:=by omega
            rw [hs3];decide
          · have hs3 : pair13Count S.D=3:=by omega
            simp [K,he3,hs3])
      have hb : 1+5*pair12Count S.D+Nat.choose (pair12Count S.D) 2+
          Nat.choose (pair13Count S.D) 2+ferrersW (pair13Count S.D) 1 1+K≤S.m := by
        simp only [max_eq_left (by omega : 1≤pair12Count S.D),max_eq_right hlong] at h
        norm_num only [Nat.choose_self] at h
        omega
      rw [fullTarget_eq_square,ht]
      exact le_trans (by simpa only [Nat.add_assoc] using ha) hb
  · exact fullSupport_t2_all_pair_two_sharp S hg hf ho ht (by have:=ho.2;omega) (by have:=ho.2;omega)

/-- The complete non-h11 branch follows from a unit-coordinate classification,
    not from an atlas or a finite candidate elimination. -/
theorem fullSupport_t2_non_h11_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (_hs : 2≤pair13Count S.D) (hne : g.y≠1 ∨ g.z≠1) : fullTarget S≤S.m := by
  by_cases hx : g.x=1
  · by_cases hp : g.y=1 ∨ g.z=1
    · exact fullSupport_t2_two_transverse_units_sharp S hg hf ho ht hx hp
    · exact fullSupport_t2_x_unit_sharp S hg hf ho ht hx
        (by have:=hf.2.1;omega) (by have:=hf.2.2;omega)
  · by_cases hy : g.y=1
    · exact fullSupport_t2_transverse_unit_sharp S hg hf ho ht (by have:=hf.1;omega)
        (Or.inl ⟨hy,by have:=hf.2.2;omega⟩)
    · by_cases hz : g.z=1
      · exact fullSupport_t2_transverse_unit_sharp S hg hf ho ht (by have:=hf.1;omega)
          (Or.inr ⟨hz,by have:=hf.2.1;omega⟩)
      · exact fullSupport_t2_no_unit_sharp S hg hf ho ht
          (by have:=hf.1;omega) (by have:=hf.2.1;omega) (by have:=hf.2.2;omega)

/-- Ordered t=2 is closed for every full-support minimal complement. -/
theorem fullSupport_t2_ordered_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2) : fullTarget S≤S.m := by
  have hs : 2≤pair13Count S.D:=by have:=ho.1;omega
  by_cases hh : g.y=1 ∧ g.z=1
  · exact fullSupport_t2_h11_sharp S hg hf ho ht hs hh.1 hh.2
  · exact fullSupport_t2_non_h11_symbolic_sharp S hg hf ho ht hs (by omega)

end NSP3
