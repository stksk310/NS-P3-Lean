import NSP3.SymbolicT3UnitYGeometry
import NSP3.SymbolicT3UnitBudget

namespace NSP3
open Finset

private theorem short_y_face_tail (C : ℕ) : C-2 ≤ ferrersPlaneDefect 3 1 C := by
  classical
  let P := (Icc 3 C).image (fun z => (1,z))
  have hsub : P ⊆ ferrersRectangle 3 1 C := by
    intro p hp
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hp
    have hz := mem_Icc.mp hz
    exact mem_filter.mpr ⟨mem_product.mpr ⟨by simp,
      mem_Icc.mpr ⟨by omega,hz.2⟩⟩,by omega⟩
  have hc : P.card=C-2 := by
    dsimp [P]
    rw [card_image_iff.mpr (fun _ _ _ _ h => congrArg Prod.snd h)]
    simp
  have h := card_le_card hsub
  rw [hc] at h
  exact le_trans h (le_trans (le_max_left _ _) (le_max_right _ _))

private theorem balanced_four_y_corners (r A : ℕ) (hr : 3 ≤ r) (ha : r ≤ A) :
    4 ≤ (ferrersRectangle r A 3).card := by
  classical
  let P : Finset (ℕ × ℕ) := {(A,1),(A,2),(A,3),(A-1,3)}
  have hsub : P ⊆ ferrersRectangle r A 3 := by
    intro p hp
    simp only [P,mem_insert,mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      apply mem_filter.mpr <;>
      refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,
        mem_Icc.mpr ⟨by omega,by omega⟩⟩,by omega⟩
  have hn : A ≠ A-1 := by omega
  have hc : P.card=4 := by simp [P,hn]
  have h := card_le_card hsub
  omega

/-- Actual H substituted into disjoint BW; the xz rectangle is charged once. -/
theorem fullSupport_t3_unit_y_resource_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hy : g.y=1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z) :
    3*pair12Count S.D+Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      g.x*g.z+min (pair12Count S.D-2) (pair13Count S.D-1)+3+
      (pair13Count S.D-1-g.x)+(pair13Count S.D-2-g.x)+
      ferrersPlaneDefect (pair12Count S.D) g.x 1+
      (ferrersRectangle (pair13Count S.D) g.x g.z).card+
      ferrersPlaneDefect 3 1 g.z ≤ S.m := by
  have hm := fullSupport_symbolic_BW_lower S hg hf ho
  have hH := t3_unit_y_H_card S hg hf ho ht hy hx hz
  have hE : (ferrersRectangle (pair13Count S.D) g.x g.z).card ≤
      ferrersPlaneDefect (pair13Count S.D) g.x g.z :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hX := le_max_left (pair12Count S.D) g.x
  have hY := le_max_left (pair12Count S.D) g.y
  have hZ := le_max_left (pair12Count S.D) g.z
  have hp : 0 < g.x*g.z := Nat.mul_pos (by omega) (by omega)
  unfold fullSupportSymbolicBW at hm
  rw [hH,ht,hy] at hm
  norm_num only [Nat.choose] at hm
  omega

/-- Capacity slack closes directly for every ordered pair of long counts. -/
theorem fullSupport_t3_unit_y_slack_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hy : g.y=1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z)
    (hcap : pair12Count S.D+2 ≤ g.x+g.z) : fullTarget S ≤ S.m := by
  let r := pair12Count S.D
  let s := pair13Count S.D
  let E := (ferrersRectangle s g.x g.z).card
  let M := ferrersPlaneDefect r g.x 1
  let T := ferrersPlaneDefect 3 1 g.z
  have hs : 3 ≤ s := by have := ho.1;dsimp [s];omega
  have hsr : s ≤ r := ho.2
  have hL : s-2 ≤ min (r-2) (s-1) := by omega
  have hE : 3 ≤ E := ferrers_rectangle_three_corners s g.x g.z hx hz (by omega)
  have hM : 1 ≤ M := le_max_left _ _
  have hT : 1 ≤ T := le_max_left _ _
  have hm := fullSupport_t3_unit_y_resource_lower S hg hf ho ht hy hx hz
  have hm' : 1+3*r+Nat.choose r 2+Nat.choose s 2+g.x*g.z+s+E+M+T ≤ S.m := by
    dsimp [r,s,E,M,T] at *
    omega
  have hv : 2*r ≤ g.x*g.z := by
    have ex : g.x-2+2=g.x := by omega
    have ez : g.z-2+2=g.z := by omega
    have hn : 0 ≤ (g.x-2)*(g.z-2) := Nat.zero_le _
    change r+2 ≤ g.x+g.z at hcap
    nlinarith only [ex,ez,hn,hcap]
  have cr : 2*Nat.choose r 2=r*(r-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2=s*(s-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r := by omega
  have es : s-1+1=s := by omega
  have hsq : (r+s+5)^2 ≤ 4*S.m := by
    by_cases he : r=s
    · have hextra : 6 ≤ E+M+T := by
        by_cases hc2 : g.z=2
        · have ht2 : T=2 := by dsimp [T];rw [hc2];decide
          omega
        · by_cases hc3 : g.z=3
          · by_cases ha : g.x+1 ≤ r
            · have hw := ferrers_unit_W_first r g.x (by omega) ha
              have hwm : ferrersW r g.x 1 ≤ M :=
                le_trans (le_max_right _ _) (le_max_right _ _)
              omega
            · have he4 : 4 ≤ E := by
                dsimp [E];rw [←he,hc3]
                exact balanced_four_y_corners r g.x (by omega) (by omega)
              omega
          · have htail : g.z-2 ≤ T := short_y_face_tail g.z
            omega
      nlinarith only [hm',hv,hextra,cr,cs,er,es,he]
    · have hd : 1 ≤ r-s := by omega
      have ed : r-s+s=r := Nat.sub_add_cancel hsr
      have hd2 : 1 ≤ (r-s)^2 := by nlinarith only [hd]
      nlinarith only [hm',hv,hE,hM,hT,cr,cs,er,es,ed,hd,hd2]
  rw [fullTarget_eq_square,ht]
  change ((r+s+3+2)^2+3)/4 ≤ S.m
  have he : r+s+3+2=r+s+5 := by omega
  rw [he];omega

/-- Every nonbalanced y-unit configuration closes by BW, without small cases. -/
theorem fullSupport_t3_unit_y_nonbalanced_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hy : g.y=1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z)
    (hrs : pair13Count S.D < pair12Count S.D) : fullTarget S ≤ S.m := by
  by_cases hslack : pair12Count S.D+2 ≤ g.x+g.z
  · exact fullSupport_t3_unit_y_slack_sharp S hg hf ho ht hy hx hz hslack
  let r := pair12Count S.D
  let s := pair13Count S.D
  let E := (ferrersRectangle s g.x g.z).card
  let M := ferrersPlaneDefect r g.x 1
  let T := ferrersPlaneDefect 3 1 g.z
  have hcap := t3_unit_y_capacity S hg hf ho hy
  have heq : g.x+g.z=r+1 := by dsimp [r];omega
  have hs : 3 ≤ s := by have := ho.1;dsimp [s];omega
  have hsr : s < r := hrs
  have hL : min (r-2) (s-1)=s-1 := by omega
  have hE : 3 ≤ E := ferrers_rectangle_three_corners s g.x g.z hx hz (by omega)
  have hM : g.x ≤ M := le_trans (ferrers_unit_W_first r g.x (by omega) (by omega))
    (le_trans (le_max_right _ _) (le_max_right _ _))
  have hT : g.z-2 ≤ T := short_y_face_tail g.z
  have hm := fullSupport_t3_unit_y_resource_lower S hg hf ho ht hy hx hz
  have hm' : 1+3*r+Nat.choose r 2+Nat.choose s 2+g.x*g.z+s+E+M+T ≤ S.m := by
    dsimp [r,s,E,M,T] at *
    omega
  have hv : 2*r ≤ g.x*g.z+2 := by
    have ex : g.x-2+2=g.x := by omega
    have ez : g.z-2+2=g.z := by omega
    have hn : 0 ≤ (g.x-2)*(g.z-2) := Nat.zero_le _
    nlinarith only [ex,ez,hn,heq]
  have hc : g.z-2+2=g.z := by omega
  have cr : 2*Nat.choose r 2=r*(r-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2=s*(s-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r := by omega
  have es : s-1+1=s := by omega
  have hd : 1 ≤ r-s := by omega
  have ed : r-s+s=r := Nat.sub_add_cancel (by omega)
  have hd2 : 1 ≤ (r-s)^2 := by nlinarith only [hd]
  have hbase : 6*r+s+1+Nat.choose r 2+Nat.choose s 2 ≤ S.m := by
    omega
  have hsq : (r+s+5)^2 ≤ 4*S.m := by
    nlinarith only [hbase,cr,cs,er,es,hs,ed,hd,hd2]
  rw [fullTarget_eq_square,ht]
  change ((r+s+3+2)^2+3)/4 ≤ S.m
  have he : r+s+3+2=r+s+5 := by omega
  rw [he];omega

end NSP3
