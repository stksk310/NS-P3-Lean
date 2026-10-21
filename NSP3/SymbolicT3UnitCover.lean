import NSP3.SymbolicT3UnitBudget
import NSP3.SymbolicT3UnitPatterns

namespace NSP3
open Finset

private theorem rectangle_positive (r A B : ℕ) (ha : 0 < A) (hb : 0 < B)
    (hcap : r < A+B) : 1 ≤ (ferrersRectangle r A B).card := by
  apply card_pos.mpr
  exact ⟨(A,B),mem_filter.mpr ⟨mem_product.mpr ⟨by simp;omega,by simp;omega⟩,hcap⟩⟩

private theorem short_face_tail (B : ℕ) : B-2 ≤ ferrersPlaneDefect 3 B 1 := by
  classical
  let P := (Icc 3 B).image (fun x => (x,1))
  have hsub : P ⊆ ferrersRectangle 3 B 1 := by
    intro p hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    have hx := mem_Icc.mp hx
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,hx.2⟩,
      by simp⟩,by omega⟩
  have hc : P.card=B-2 := by
    dsimp [P]
    rw [card_image_iff.mpr (fun _ _ _ _ h => congrArg Prod.fst h)]
    simp
  have h := card_le_card hsub
  rw [hc] at h
  exact le_trans h (le_trans (le_max_left _ _) (le_max_right _ _))

set_option maxHeartbeats 2000000 in
private theorem equality_cover (r s A B E M T m : ℕ)
    (hs : 3 ≤ s) (hsr : s ≤ r) (hA : 2 ≤ A) (hB : 2 ≤ B) (hcap : A+B=r+1)
    (hm : 1+3*r+Nat.choose r 2+Nat.choose s 2+A*B+s+
      (s-1-A)+(min (r-2) (s-1)-A)+E+M+T ≤ m)
    (hE : 1 ≤ E) (hM : 1 ≤ M) (hT : 1 ≤ T)
    (hMW : A+1 ≤ s → A ≤ M) (hMW2 : A+2 ≤ s → 2*A ≤ M)
    (hTail : B-2 ≤ T) (hT2 : B=2 → 2 ≤ T) :
    (r+s+5)^2 ≤ 4*m ∨
      (s=r-1 ∧ A=r-1 ∧ B=2) ∨
      (r=4 ∧ s=3 ∧ A=2 ∧ B=3) ∨
      (r=s ∧ r≤5 ∧ A=r-1 ∧ B=2) ∨
      (r=4 ∧ s=4 ∧ A=2 ∧ B=3) := by
  have cr : 2*Nat.choose r 2=r*(r-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2=s*(s-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r := by omega
  have es : s-1+1=s := by omega
  have ev' : 2*r ≤ A*B+2 := by
    have ea : A-2+2=A := by omega
    have eb : B-2+2=B := by omega
    have en : 0 ≤ (A-2)*(B-2) := Nat.zero_le _
    nlinarith only [ea,eb,en,hcap]
  by_cases hfar : s+2 ≤ r
  · left
    have ed : r-s+s=r := Nat.sub_add_cancel hsr
    have hd : 2 ≤ r-s := by omega
    have hd2 : 4 ≤ (r-s)^2 := by nlinarith only [hd]
    nlinarith only [hm,ev',hE,hM,hT,cr,cs,er,es,ed,hd,hd2]
  · by_cases he : r=s
    · by_cases hb2 : B=2
      · by_cases hr : 6 ≤ r
        · left
          have hmA := hMW (by omega)
          have ht2 := hT2 hb2
          nlinarith only [hm,ev',hmA,ht2,hE,cr,cs,er,es,he,hcap,hb2,hr]
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨he,by omega,by omega,hb2⟩)))
      · by_cases hb3 : B=3
        · by_cases hr : 5 ≤ r
          · left
            have hm2 := hMW2 (by omega)
            nlinarith only [hm,hm2,hE,hT,cr,cs,er,es,he,hcap,hb3,hr]
          · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega,by omega,by omega,hb3⟩)))
        · left
          have hb4 : 4 ≤ B := by omega
          have hmA := hMW (by omega)
          have eU1 : s-1-A = B-2 := by omega
          have eU2 : min (r-2) (s-1)-A = B-3 := by omega
          have eB2 : B-2+2=B := by omega
          have eB3 : B-3+3=B := by omega
          have hr5 : 5 ≤ r := by omega
          nlinarith only [hm,ev',hmA,hTail,hE,cr,cs,er,es,he,hcap,hb4,
            eU1,eU2,eB2,eB3,hr5]
    · have hnear : r=s+1 := by omega
      by_cases hlast : A=r-1
      · exact Or.inr (Or.inl ⟨by omega,hlast,by omega⟩)
      · have hAs : A+1 ≤ s := by omega
        have hmA := hMW hAs
        have eB : B-2+2=B := by omega
        by_cases hr : 5 ≤ r
        · left
          nlinarith only [hm,ev',hmA,hTail,hE,cr,cs,er,es,hnear,hcap,eB,hr]
        · exact Or.inr (Or.inr (Or.inl ⟨by omega,by omega,by omega,by omega⟩))

/-- Infinite symbolic z-unit coverage: only five explicit small placements
remain after integrating the frozen infinite near-balanced exception. -/
theorem fullSupport_t3_unit_z_symbolic_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hz : g.z = 1) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) :
    fullTarget S ≤ S.m ∨
      (pair12Count S.D = 4 ∧ pair13Count S.D = 3 ∧ g.x = 2 ∧ g.y = 3) ∨
      (pair12Count S.D = pair13Count S.D ∧ pair12Count S.D ≤ 5 ∧
        g.x = pair12Count S.D-1 ∧ g.y = 2) ∨
      (pair12Count S.D = 4 ∧ pair13Count S.D = 4 ∧ g.x = 2 ∧ g.y = 3) := by
  by_cases hslack : pair12Count S.D+2 ≤ g.x+g.y
  · exact Or.inl (fullSupport_t3_unit_z_slack_sharp S hg hf ho ht hz hx hy hslack)
  have hcap := t3_unit_z_capacity S hg hf ho hz
  have heq : g.x+g.y=pair12Count S.D+1 := by omega
  have hs : 3 ≤ pair13Count S.D := by have := ho.1;omega
  have hsr := ho.2
  have hm := fullSupport_t3_unit_z_resource_lower S hg hf ho ht hz hx hy
  let E := (ferrersRectangle (pair12Count S.D) g.x g.y).card
  let M := ferrersPlaneDefect (pair13Count S.D) g.x 1
  let T := ferrersPlaneDefect 3 g.y 1
  have hE : 1 ≤ E := rectangle_positive _ _ _ (by omega) (by omega) (by omega)
  have hM : 1 ≤ M := le_max_left _ _
  have hT : 1 ≤ T := le_max_left _ _
  have hMW : g.x+1 ≤ pair13Count S.D → g.x ≤ M := by
    intro ha
    exact le_trans (ferrers_unit_W_first _ _ (by omega) ha)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hMW2 : g.x+2 ≤ pair13Count S.D → 2*g.x ≤ M := by
    intro ha
    exact le_trans (ferrers_unit_W_two _ _ (by omega) ha)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hTail : g.y-2 ≤ T := short_face_tail g.y
  have hT2 : g.y=2 → 2 ≤ T := by
    intro ha
    dsimp [T];rw [ha];decide
  obtain hsq | hnear | h433 | hbal | h443 := equality_cover
    (pair12Count S.D) (pair13Count S.D) g.x g.y E M T S.m
    hs hsr hx hy heq hm hE hM hT hMW hMW2 hTail hT2
  · left
    rw [fullTarget_eq_square,ht]
    have he : pair12Count S.D+pair13Count S.D+3+2=
        pair12Count S.D+pair13Count S.D+5 := by omega
    rw [he];omega
  · left
    exact fullSupport_t3_one_unit_exception_sharp S hg hf ho ht
      (by omega) hnear.1 hnear.2.1 hnear.2.2 hz
  · exact Or.inr (Or.inl h433)
  · exact Or.inr (Or.inr (Or.inl hbal))
  · exact Or.inr (Or.inr (Or.inr h443))

end NSP3
