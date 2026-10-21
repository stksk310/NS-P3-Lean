import NSP3.SymbolicT3UnitGeometry

namespace NSP3
open Finset

/-- The first term of a unit face already contributes A. -/
theorem ferrers_unit_W_first (r A : ℕ) (ha : 0 < A) (hr : A+1 ≤ r) :
    A ≤ ferrersW r A 1 := by
  have hm : A ∈ Icc A (r-1) := mem_Icc.mpr ⟨le_rfl,by omega⟩
  have h := single_le_sum (f := fun i => min (A*(r-i)) (1*i))
    (fun _ _ => Nat.zero_le _) hm
  have he : min (A*(r-A)) (1*A) = A := by
    have hmul := Nat.mul_le_mul_left A (show 1 ≤ r-A by omega)
    simp only [mul_one,one_mul] at *
    omega
  change min (A*(r-A)) (1*A) ≤ ferrersW r A 1 at h
  rwa [he] at h

/-- Two distinct initial terms supply two copies of A, counted once each. -/
theorem ferrers_unit_W_two (r A : ℕ) (ha : 0 < A) (hr : A+2 ≤ r) :
    2*A ≤ ferrersW r A 1 := by
  let f := fun i => min (A*(r-i)) (1*i)
  have hsub : ({A,A+1} : Finset ℕ) ⊆ Icc A (r-1) := by
    intro i hi
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact mem_Icc.mpr ⟨by omega,by omega⟩
  have h := sum_le_sum_of_subset (f:=f) hsub
  have h0 : A ≤ f A := by
    have hm := Nat.mul_le_mul_left A (show 1 ≤ r-A by omega)
    dsimp [f]; simp only [mul_one,one_mul] at *; omega
  have h1 : A ≤ f (A+1) := by
    have hm := Nat.mul_le_mul_left A (show 1 ≤ r-(A+1) by omega)
    dsimp [f]; simp only [mul_one,one_mul] at *; omega
  have hn : A ∉ ({A+1} : Finset ℕ) := by simp
  simp only [sum_insert hn,sum_singleton] at h
  change f A + f (A+1) ≤ ferrersW r A 1 at h
  omega

/-- Capacity slack forces three distinct rectangle-excess corners. -/
theorem ferrers_rectangle_three_corners (r A B : ℕ) (ha : 2 ≤ A) (hb : 2 ≤ B)
    (hcap : r+2 ≤ A+B) : 3 ≤ (ferrersRectangle r A B).card := by
  classical
  let P : Finset (ℕ × ℕ) := {(A,B),(A-1,B),(A,B-1)}
  have hsub : P ⊆ ferrersRectangle r A B := by
    intro p hp
    simp only [P,mem_insert,mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;>
      apply mem_filter.mpr <;>
      refine ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,
        mem_Icc.mpr ⟨by omega,by omega⟩⟩,by omega⟩
  have hA : A-1 ≠ A := by omega
  have hB : B-1 ≠ B := by omega
  have hc : P.card = 3 := by simp [P,hA,hB,Ne.symm hA,Ne.symm hB]
  have h := card_le_card hsub
  omega

private theorem unit_rectangle_card (r A : ℕ) (hr : 1 ≤ r) :
    (ferrersRectangle r A 1).card = A+1-r := by
  classical
  have he : ferrersRectangle r A 1 = (Icc r A).image (fun x => (x,1)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hm,hs⟩ := mem_filter.mp hp
      obtain ⟨hA,hB⟩ := mem_product.mp hm
      have hA := mem_Icc.mp hA
      have hB := mem_Icc.mp hB
      exact mem_image.mpr ⟨p.1,mem_Icc.mpr ⟨by omega,hA.2⟩,Prod.ext rfl (by omega)⟩
    · intro hp
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
      have hx := mem_Icc.mp hx
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,hx.2⟩,
        by simp⟩,by omega⟩
  rw [he,card_image_iff.mpr (fun _ _ _ _ h => congrArg Prod.fst h)]
  simp

private theorem balanced_four_corners (r A : ℕ) (hr : 3 ≤ r) (ha : r ≤ A) :
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
  have hc : P.card = 4 := by simp [P,hn]
  have h := card_le_card hsub
  omega

/-- Z1 from the actual H identity and existing disjoint BW resource theorem. -/
theorem fullSupport_t3_unit_z_resource_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hz : g.z = 1) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) :
    1 + 3*pair12Count S.D + Nat.choose (pair12Count S.D) 2 +
      Nat.choose (pair13Count S.D) 2 + g.x*g.y + pair13Count S.D +
      (pair13Count S.D-1-g.x) +
      (min (pair12Count S.D-2) (pair13Count S.D-1)-g.x) +
      (ferrersRectangle (pair12Count S.D) g.x g.y).card +
      ferrersPlaneDefect (pair13Count S.D) g.x 1 + ferrersPlaneDefect 3 g.y 1 ≤ S.m := by
  have hm := fullSupport_symbolic_BW_lower S hg hf ho
  have hH := t3_unit_z_H_card S hg hf ho ht hz hx hy
  have hE : (ferrersRectangle (pair12Count S.D) g.x g.y).card ≤
      ferrersPlaneDefect (pair12Count S.D) g.x g.y :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hX := le_max_left (pair12Count S.D) g.x
  have hY := le_max_left (pair12Count S.D) g.y
  have hZ := le_max_left (pair12Count S.D) g.z
  have hs : 3 ≤ pair13Count S.D := by have := ho.1; omega
  have hp : 0 < g.x*g.y := Nat.mul_pos (by omega) (by omega)
  unfold fullSupportSymbolicBW at hm
  rw [ht,hz,hH] at hm
  norm_num only [Nat.choose] at hm
  omega

/-- Every capacity-slack z-unit configuration is sharp, for all ordered counts. -/
theorem fullSupport_t3_unit_z_slack_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hz : g.z = 1) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y)
    (hcap : pair12Count S.D+2 ≤ g.x+g.y) : fullTarget S ≤ S.m := by
  let r := pair12Count S.D
  let s := pair13Count S.D
  let E := (ferrersRectangle r g.x g.y).card
  let M := ferrersPlaneDefect s g.x 1
  let T := ferrersPlaneDefect 3 g.y 1
  have hs : 3 ≤ s := by have := ho.1; dsimp [s]; omega
  have hsr : s ≤ r := ho.2
  have hE : 3 ≤ E := ferrers_rectangle_three_corners r g.x g.y hx hy hcap
  have hM : 1 ≤ M := le_max_left _ _
  have hT : 1 ≤ T := le_max_left _ _
  have hm := fullSupport_t3_unit_z_resource_lower S hg hf ho ht hz hx hy
  have hm' : 1+3*r+Nat.choose r 2+Nat.choose s 2+g.x*g.y+s+E+M+T ≤ S.m := by
    dsimp [r,s,E,M,T] at *
    omega
  have hv : 2*r ≤ g.x*g.y := by
    have ex : g.x-2+2=g.x := by omega
    have ey : g.y-2+2=g.y := by omega
    have hn : 0 ≤ (g.x-2)*(g.y-2) := Nat.zero_le _
    change r+2 ≤ g.x+g.y at hcap
    nlinarith only [ex,ey,hn,hcap]
  have cr : 2*Nat.choose r 2 = r*(r-1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2 = s*(s-1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r := by omega
  have es : s-1+1=s := by omega
  have hsq : (r+s+5)^2 ≤ 4*S.m := by
    by_cases he : r=s
    · have hextra : 6 ≤ E+M+T := by
        by_cases hb2 : g.y=2
        · have ht2 : T=2 := by dsimp [T];rw [hb2];decide
          omega
        · by_cases hb3 : g.y=3
          · by_cases ha : g.x+1 ≤ r
            · have hw := ferrers_unit_W_first r g.x (by omega) ha
              have hwm : ferrersW r g.x 1 ≤ M := by
                dsimp [M];rw [←he];exact le_trans (le_max_right _ _) (le_max_right _ _)
              omega
            · have he4 : 4 ≤ E := by
                dsimp [E];rw [hb3];exact balanced_four_corners r g.x (by omega) (by omega)
              omega
          · have hre : (ferrersRectangle 3 g.y 1).card ≤ T :=
              le_trans (le_max_left _ _) (le_max_right _ _)
            rw [unit_rectangle_card 3 g.y (by decide)] at hre
            omega
      nlinarith only [hm',hv,hextra,cr,cs,er,es,he]
    · have hd : 1 ≤ r-s := by omega
      have ed : r-s+s=r := Nat.sub_add_cancel hsr
      have hd2 : 1 ≤ (r-s)^2 := by nlinarith only [hd]
      nlinarith only [hm',hv,hE,hM,hT,cr,cs,er,es,ed,hd,hd2]
  rw [fullTarget_eq_square,ht]
  change ((r+s+3+2)^2+3)/4 ≤ S.m
  have he : r+s+3+2=r+s+5 := by omega
  rw [he]
  omega

end NSP3
