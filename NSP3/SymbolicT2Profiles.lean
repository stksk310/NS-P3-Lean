import NSP3.SymbolicThin23Balanced

namespace NSP3
open Finset

/-- The positive punctured box is an actual subset of H, regardless of core overlap. -/
theorem positive_box_H_lower (S : CyclicStaircase) (g : Point3)
    (hf : FullSupport g) : g.x*g.y*g.z-1 ≤ (fullSupportSymbolicH S g).card := by
  classical
  let P := (Icc 1 g.x).product ((Icc 1 g.y).product (Icc 1 g.z))
  let f : ℕ × (ℕ × ℕ) → Point3 := fun a => ⟨a.1,a.2.1,a.2.2⟩
  have hi : Set.InjOn f P := by
    intro a _ b _ he
    exact Prod.ext (congrArg Point3.x he)
      (Prod.ext (congrArg Point3.y he) (congrArg Point3.z he))
  have hc : (P.image f).card=g.x*g.y*g.z := by
    rw [card_image_of_injOn hi]
    simp [P,Nat.mul_assoc]
  have hm : g ∈ P.image f := by
    have hx := hf.1
    have hy := hf.2.1
    have hz := hf.2.2
    exact mem_image.mpr ⟨(g.x,(g.y,g.z)),by simp [P]; omega,rfl⟩
  have hsub : (P.image f).erase g ⊆ fullSupportSymbolicH S g := by
    intro p hp
    obtain ⟨hne,hp⟩ := mem_erase.mp hp
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hp
    obtain ⟨hxl,hxu,hyl,hyu,hzl,hzu⟩ := (show 1≤a.1 ∧ a.1≤g.x ∧
        1≤a.2.1 ∧ a.2.1≤g.y ∧ 1≤a.2.2 ∧ a.2.2≤g.z by
      simpa [P,mem_product,mem_Icc,and_assoc] using ha)
    apply mem_union.mpr; right
    exact mem_filter.mpr ⟨(mem_lowerBoxFinset _ _).mpr
      ⟨⟨hxu,hyu,hzu⟩,hne⟩,⟨hxl,hyl,hzl⟩⟩
  have h:=card_le_card hsub
  rw [card_erase_of_mem hm,hc] at h
  exact h

private theorem punctured_box_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) :
    (g.x+1)*(g.y+1)*(g.z+1)-1≤S.m := by
  have h:=card_le_card (lowerBoxFinset_subset_D hg)
  simpa only [card_lowerBoxFinset,S.card_D] using h

private theorem bw_positive_box_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2) :
    3*pair12Count S.D+Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+g.x*g.y*g.z+4≤S.m := by
  have h:=fullSupport_symbolic_BW_lower S hg hf ho
  have hb:=positive_box_H_lower S g hf
  have hpos:=Nat.mul_pos (Nat.mul_pos hf.1 hf.2.1) hf.2.2
  have h12 : 1≤ferrersPlaneDefect (pair12Count S.D) g.x g.y:=le_max_left _ _
  have h13 : 1≤ferrersPlaneDefect (pair13Count S.D) g.x g.z:=le_max_left _ _
  have h23 : 1≤ferrersPlaneDefect (pair23Count S.D) g.y g.z:=le_max_left _ _
  have hx:=le_max_left (pair12Count S.D) g.x
  have hy:=le_max_left (pair12Count S.D) g.y
  have hz:=le_max_left (pair12Count S.D) g.z
  unfold fullSupportSymbolicBW at h
  rw [ht] at h h23
  norm_num at h
  omega

private theorem product_three_lower (A B C : ℕ) (hA : 2≤A) (hB : 2≤B)
    (hC : 2≤C) : 4*(A+B+C-4)≤A*B*C := by
  have ha : A-2+2=A:=by omega
  have hb : B-2+2=B:=by omega
  have hc : C-2+2=C:=by omega
  have hab := Nat.zero_le ((A-2)*(B-2))
  have hab4 : 4≤A*B := by nlinarith
  have habc := Nat.mul_le_mul_right (C-2) hab4
  have hsum : A+B+C-4+4=A+B+C:=by omega
  nlinarith

private theorem no_unit_arithmetic (r s P : ℕ) (hr : 4 ≤ r) (hs : 2 ≤ s)
    (ho : s ≤ r) (hp : 4*(r-2) ≤ P) :
    ((r+s+4)^2+3)/4≤3*r+Nat.choose r 2+Nat.choose s 2+P+4 := by
  have cr : 2*Nat.choose r 2=r*(r-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2=s*(s-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r:=by omega
  have es : s-1+1=s:=by omega
  have e2 : r-2+2=r:=by omega
  have ed : r-s+s=r:=Nat.sub_add_cancel ho
  have hn : (r+s+4)^2≤4*(3*r+Nat.choose r 2+Nat.choose s 2+P+4) := by
    nlinarith [Nat.zero_le ((r-s)^2)]
  omega

/-- Every all-nonunit full-support t2 boundary satisfies the sharp target. -/
theorem fullSupport_t2_no_unit_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hx : 2≤g.x) (hy : 2≤g.y) (hz : 2≤g.z) : fullTarget S≤S.m := by
  have hs : 2≤pair13Count S.D:=by have:=ho.1;omega
  by_cases hr : 4≤pair12Count S.D
  · have hcap:=pair12_terminal_return_capacity_ordered S hg hf ho
    have hp0:=product_three_lower g.x g.y g.z hx hy hz
    have hp : 4*(pair12Count S.D-2)≤g.x*g.y*g.z := by omega
    have ha:=no_unit_arithmetic (pair12Count S.D) (pair13Count S.D)
      (g.x*g.y*g.z) hr hs ho.2 hp
    have hb:=bw_positive_box_lower S hg hf ho ht
    rw [fullTarget_eq_square,ht]
    simpa only [Nat.add_assoc] using le_trans ha hb
  · have hb:=punctured_box_lower S hg
    have hp:=Nat.mul_le_mul (Nat.mul_le_mul
      (show 3≤g.x+1 by omega) (show 3≤g.y+1 by omega)) (show 3≤g.z+1 by omega)
    have hr3 : pair12Count S.D≤3:=by omega
    have hs3 : pair13Count S.D≤3:=by have:=ho.2;omega
    have hsquare : (pair12Count S.D+pair13Count S.D+4)^2≤100:=by nlinarith
    rw [fullTarget_eq_square,ht]
    norm_num only [Nat.add_assoc] at *
    omega

/-- A hypothetical failure must have a unit coordinate; no classifier is assumed. -/
theorem fullSupport_t2_unit_profile_split (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2) :
    g.x=1 ∨ g.y=1 ∨ g.z=1 ∨ fullTarget S≤S.m := by
  by_cases hx : g.x=1
  · exact Or.inl hx
  by_cases hy : g.y=1
  · exact Or.inr (Or.inl hy)
  by_cases hz : g.z=1
  · exact Or.inr (Or.inr (Or.inl hz))
  exact Or.inr (Or.inr (Or.inr (fullSupport_t2_no_unit_sharp S hg hf ho ht
    (by have:=hf.1;omega) (by have:=hf.2.1;omega) (by have:=hf.2.2;omega))))

end NSP3
