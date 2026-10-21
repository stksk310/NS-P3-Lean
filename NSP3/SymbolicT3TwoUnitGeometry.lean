import NSP3.SymbolicT3UnitXIntegration

namespace NSP3
open Finset

private def row (hi y z : ℕ) : Finset Point3 :=
  (Icc 1 hi).image (fun x => Point3.mk x y z)

private theorem mem_row (hi y z : ℕ) (p : Point3) :
    p ∈ row hi y z ↔ 1 ≤ p.x ∧ p.x ≤ hi ∧ p.y=y ∧ p.z=z := by
  constructor
  · intro hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    exact ⟨(mem_Icc.mp hx).1,(mem_Icc.mp hx).2,rfl,rfl⟩
  · rintro ⟨hl,hu,hy,hz⟩
    exact mem_image.mpr ⟨p.x,mem_Icc.mpr ⟨hl,hu⟩,by ext <;> simp_all⟩

private theorem card_row (hi y z : ℕ) : (row hi y z).card=hi := by
  unfold row
  rw [card_image_iff.mpr (fun _ _ _ _ h => congrArg Point3.x h)]
  simp

/-- The complete positive t3 core has three literal rows, including balanced endpoints. -/
theorem t3_fullCore_card_exact (S : CyclicStaircase) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) :
    (fullCoreFinset S).card=(pair13Count S.D-1)+(pair13Count S.D-2)+
      min (pair12Count S.D-2) (pair13Count S.D-1) := by
  classical
  let R := row (pair13Count S.D-1) 1 1
  let T := row (pair13Count S.D-2) 1 2
  let U := row (min (pair12Count S.D-2) (pair13Count S.D-1)) 2 1
  have hs : 3 ≤ pair13Count S.D := by have := ho.1; omega
  have he : fullCoreFinset S=(R ∪ T) ∪ U := by
    ext p
    simp only [mem_fullCoreFinset,mem_union]
    have hR := mem_row (pair13Count S.D-1) 1 1 p
    have hT := mem_row (pair13Count S.D-2) 1 2 p
    have hU := mem_row (min (pair12Count S.D-2) (pair13Count S.D-1)) 2 1 p
    simp only [FullCore,ht]
    change _ ↔ (p ∈ row (pair13Count S.D-1) 1 1 ∨
      p ∈ row (pair13Count S.D-2) 1 2) ∨
      p ∈ row (min (pair12Count S.D-2) (pair13Count S.D-1)) 2 1
    rw [hR,hT,hU]
    have := ho.2
    omega
  have hd : Disjoint R T := by
    apply disjoint_left.mpr
    intro p hr ht'
    have := (mem_row _ _ _ p).mp hr
    have := (mem_row _ _ _ p).mp ht'
    omega
  have hd' : Disjoint (R ∪ T) U := by
    apply disjoint_left.mpr
    intro p hp hu
    have hu := (mem_row _ _ _ p).mp hu
    rcases mem_union.mp hp with hp | hp
    all_goals have := (mem_row _ _ _ p).mp hp; omega
  rw [he,card_union_of_disjoint hd',card_union_of_disjoint hd]
  simp only [R,T,U,card_row]

/-- The positive box overlaps the t3 core in exactly two points on either unit axis. -/
theorem t3_two_unit_H_card (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hu : g.y=1 ∨ g.z=1) :
    (fullSupportSymbolicH S g).card+6=g.y+g.z-1+
      2*pair13Count S.D+min (pair12Count S.D-2) (pair13Count S.D-1) := by
  classical
  let C := fullCoreFinset S
  let B := (lowerBoxFinset g).filter FullSupport
  have hc := pair12_terminal_return_capacity_ordered S hg hf ho
  have hs : 3 ≤ pair13Count S.D := by have := ho.1; omega
  have hr : 3 ≤ pair12Count S.D := by have := ho.2; omega
  have he : fullSupportSymbolicH S g=C ∪ B := by
    ext p
    simp only [fullSupportSymbolicH,mem_union,mem_puncturedFullCoreFinset,
      C,mem_fullCoreFinset]
    constructor
    · rintro (⟨h,_⟩ | h)
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · left; refine ⟨h,?_⟩
        intro hl
        have hyz := h.2.2.2.2.2
        have := hl.2.1; have := hl.2.2
        omega
      · exact Or.inr h
  have hb : B.card=g.y+g.z-2 := by
    rcases hu with hy | hz
    · have heB : B=(Icc 1 (g.z-1)).image (fun z => Point3.mk 1 1 z) := by
        ext p
        simp only [B,mem_filter,mem_lowerBoxFinset,mem_image,mem_Icc,FullSupport]
        constructor
        · rintro ⟨⟨hl,hn⟩,hp⟩
          have hpx := hl.1; have hpy := hl.2.1; have hpz := hl.2.2
          refine ⟨p.z,⟨hp.2.2,?_⟩,?_⟩
          · have hpx := hl.1; have hpy := hl.2.1; have hpz := hl.2.2
            have hne : p.z ≠ g.z := by intro e; apply hn; apply Point3.ext <;> omega
            omega
          · apply Point3.ext <;> simp only <;> omega
        · rintro ⟨z,⟨hl,hu⟩,rfl⟩
          change ((1 ≤ g.x ∧ 1 ≤ g.y ∧ z ≤ g.z) ∧ Point3.mk 1 1 z ≠ g) ∧
            (0<1 ∧ 0<1 ∧ 0<z)
          refine ⟨⟨⟨by omega,by omega,by omega⟩,?_⟩,⟨by omega,by omega,hl⟩⟩
          intro heq; have := congrArg Point3.z heq; simp only at this; omega
      rw [heB,card_image_iff.mpr (fun _ _ _ _ h => congrArg Point3.z h)]
      simp; omega
    · have heB : B=(Icc 1 (g.y-1)).image (fun y => Point3.mk 1 y 1) := by
        ext p
        simp only [B,mem_filter,mem_lowerBoxFinset,mem_image,mem_Icc,FullSupport]
        constructor
        · rintro ⟨⟨hl,hn⟩,hp⟩
          have hpx := hl.1; have hpy := hl.2.1; have hpz := hl.2.2
          refine ⟨p.y,⟨hp.2.1,?_⟩,?_⟩
          · have hpx := hl.1; have hpy := hl.2.1; have hpz := hl.2.2
            have hne : p.y ≠ g.y := by intro e; apply hn; apply Point3.ext <;> omega
            omega
          · apply Point3.ext <;> simp only <;> omega
        · rintro ⟨y,⟨hl,hu⟩,rfl⟩
          change ((1 ≤ g.x ∧ y ≤ g.y ∧ 1 ≤ g.z) ∧ Point3.mk 1 y 1 ≠ g) ∧
            (0<1 ∧ 0<y ∧ 0<1)
          refine ⟨⟨⟨by omega,by omega,by omega⟩,?_⟩,⟨by omega,hl,by omega⟩⟩
          intro heq; have := congrArg Point3.y heq; simp only at this; omega
      rw [heB,card_image_iff.mpr (fun _ _ _ _ h => congrArg Point3.y h)]
      simp; omega
  have hi : (C ∩ B).card=2 := by
    rcases hu with hy | hz
    · have hei : C ∩ B={Point3.mk 1 1 1,Point3.mk 1 1 2} := by
        ext p
        simp only [mem_inter,C,mem_fullCoreFinset,B,mem_filter,mem_lowerBoxFinset,
          mem_insert,mem_singleton,FullCore,FullSupport,ht]
        constructor
        · rintro ⟨h,⟨⟨hl,_⟩,_⟩⟩
          have := hl.1; have := hl.2.1
          have hcases : p.z=1 ∨ p.z=2 := by omega
          rcases hcases with h1 | h2
          · left; apply Point3.ext <;> simp only <;> omega
          · right; apply Point3.ext <;> simp only <;> omega
        · rintro (rfl | rfl)
          all_goals dsimp only; constructor
          all_goals try omega
          all_goals
            refine ⟨⟨?_,?_⟩,by omega⟩
            · change 1 ≤ g.x ∧ 1 ≤ g.y ∧ _ ≤ g.z
              dsimp only [Point3.z]
              omega
            · intro h
              have he := congrArg Point3.z h
              simp only at he
              omega
      rw [hei]; decide
    · have hei : C ∩ B={Point3.mk 1 1 1,Point3.mk 1 2 1} := by
        ext p
        simp only [mem_inter,C,mem_fullCoreFinset,B,mem_filter,mem_lowerBoxFinset,
          mem_insert,mem_singleton,FullCore,FullSupport,ht]
        constructor
        · rintro ⟨h,⟨⟨hl,_⟩,_⟩⟩
          have := hl.1; have := hl.2.2
          have hcases : p.y=1 ∨ p.y=2 := by omega
          rcases hcases with h1 | h2
          · left; apply Point3.ext <;> simp only <;> omega
          · right; apply Point3.ext <;> simp only <;> omega
        · rintro (rfl | rfl)
          all_goals dsimp only; constructor
          all_goals try omega
          all_goals
            refine ⟨⟨?_,?_⟩,by omega⟩
            · change 1 ≤ g.x ∧ _ ≤ g.y ∧ 1 ≤ g.z
              dsimp only [Point3.y]
              omega
            · intro h
              have he := congrArg Point3.y h
              simp only at he
              omega
      rw [hei]; decide
  have hh := card_union_add_card_inter C B
  have hC := t3_fullCore_card_exact S ho ht
  rw [←he,hi,hb] at hh
  change C.card=_ at hC
  omega

end NSP3
