import NSP3.SymbolicTGE4Rows
import NSP3.CoreHoleCap
import NSP3.FullTarget

namespace NSP3

theorem ferrers_weighted_four_small_triangle_lower (A B C : ℕ)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hA3 : A ≤ 3) (hB3 : B ≤ 3) (hC3 : C ≤ 3) :
    8 ≤ max (ferrersPlaneDefect 4 A B) (rankCutPhi 4 A B)+
      max (ferrersPlaneDefect 4 A C) (rankCutPhi 4 A C)+
      max (ferrersPlaneDefect 4 B C) (rankCutPhi 4 B C) := by
  interval_cases A <;> interval_cases B <;> interval_cases C <;> decide

private theorem small_axis_resources (B C : ℕ) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hB3 : B ≤ 3) (hC3 : C ≤ 3) (hne : B ≠ 1 ∨ C ≠ 1) :
    7 ≤ (ferrersRectangle 4 4 B).card+(ferrersRectangle 4 4 C).card+
      max (ferrersPlaneDefect 4 B C) (rankCutPhi 4 B C) := by
  interval_cases B <;> interval_cases C <;> first | decide | omega

private theorem small_rect_sym (B : ℕ) (hB : 1 ≤ B) (hB3 : B ≤ 3) :
    (ferrersRectangle 4 B 4).card=(ferrersRectangle 4 4 B).card := by
  interval_cases B <;> decide

private theorem rectangle_lower (r A B a b : ℕ) (ha : a ≤ A) (hb : b ≤ B) :
    (ferrersRectangle r a b).card ≤ ferrersPlaneDefect r A B := by
  have hsub : ferrersRectangle r a b ⊆ ferrersRectangle r A B := by
    intro p hp
    have h := Finset.mem_filter.mp hp
    have hpair := Finset.mem_product.mp h.1
    have hx := Finset.mem_Icc.mp hpair.1
    have hy := Finset.mem_Icc.mp hpair.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hx.1,le_trans hx.2 ha⟩,
       Finset.mem_Icc.mpr ⟨hy.1,le_trans hy.2 hb⟩⟩,h.2⟩
  exact le_trans (Finset.card_le_card hsub)
    (le_trans (le_max_left _ _) (le_max_right _ _))

private theorem defect_large_left (A B : ℕ) (ha : 4 ≤ A) (hb : 2 ≤ B) :
    3 ≤ ferrersPlaneDefect 4 A B := by
  have h := rectangle_lower 4 A B 4 2 ha hb
  have hc : (ferrersRectangle 4 4 2).card=3 := by decide
  simpa only [hc] using h

private theorem defect_large_right (A B : ℕ) (ha : 2 ≤ A) (hb : 4 ≤ B) :
    3 ≤ ferrersPlaneDefect 4 A B := by
  have h := rectangle_lower 4 A B 2 4 ha hb
  have hc : (ferrersRectangle 4 2 4).card=3 := by decide
  simpa only [hc] using h

private theorem defect_two_large (A B : ℕ) (ha : 4 ≤ A) (hb : 4 ≤ B) :
    10 ≤ ferrersPlaneDefect 4 A B := by
  have h := rectangle_lower 4 A B 4 4 ha hb
  have hc : (ferrersRectangle 4 4 4).card=10 := by decide
  simpa only [hc] using h

/-- A coordinate-size classification, not a residual-profile checker. -/
theorem fullSupport_q444_BF_sharp_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hr : pair12Count S.D=4) (hs : pair13Count S.D=4) (ht : pair23Count S.D=4) :
    49 ≤ fullSupportSymbolicBF S g := by
  classical
  have hx : 1 ≤ g.x := hf.1
  have hy : 1 ≤ g.y := hf.2.1
  have hz : 1 ≤ g.z := hf.2.2
  have hcore := fullCore_q444_card S hr hs ht
  have hhole := coreHole_card_le_largeHoleCap S hg hf ho
  have hpart := card_fullCore_partition S g
  have hpunct : (puncturedFullCoreFinset S g).card ≤ (fullSupportSymbolicH S g).card :=
    Finset.card_le_card (by intro p hp; exact Finset.mem_union.mpr (Or.inl hp))
  norm_num [ht,largeHoleCap] at hhole
  have hH10 : 10 ≤ (fullSupportSymbolicH S g).card := by omega
  have hHlarge (h : 4 ≤ g.x ∨ 4 ≤ g.y ∨ 4 ≤ g.z) :
      11 ≤ (fullSupportSymbolicH S g).card := by
    have hc := Finset.card_le_card (fullCore_subset_symbolic_H_of_large_coordinate S g
      (by simpa [hr,hs] using h))
    omega
  have ax := le_max_left 4 g.x
  have ay := le_max_left 4 g.y
  have az := le_max_left 4 g.z
  have dxy : 1 ≤ ferrersPlaneDefect 4 g.x g.y := le_max_left _ _
  have dxz : 1 ≤ ferrersPlaneDefect 4 g.x g.z := le_max_left _ _
  have dyz : 1 ≤ ferrersPlaneDefect 4 g.y g.z := le_max_left _ _
  have m11 : max (ferrersPlaneDefect 4 1 1) (rankCutPhi 4 1 1)=4 := by decide
  have hlxy := le_max_left (ferrersPlaneDefect 4 g.x g.y) (rankCutPhi 4 g.x g.y)
  have hlxz := le_max_left (ferrersPlaneDefect 4 g.x g.z) (rankCutPhi 4 g.x g.z)
  have hlyz := le_max_left (ferrersPlaneDefect 4 g.y g.z) (rankCutPhi 4 g.y g.z)
  have hbase : 1+max 4 g.x+max 4 g.y+max 4 g.z+(fullSupportSymbolicH S g).card+
      18+max (ferrersPlaneDefect 4 g.x g.y) (rankCutPhi 4 g.x g.y)+
      max (ferrersPlaneDefect 4 g.x g.z) (rankCutPhi 4 g.x g.z)+
      max (ferrersPlaneDefect 4 g.y g.z) (rankCutPhi 4 g.y g.z)+
      fullSupportAxisGain S g ≤ fullSupportSymbolicBF S g := by
    unfold fullSupportSymbolicBF fullSupportSymbolicBW
    rw [hr,hs,ht]
    norm_num only [Nat.choose]
    omega
  have gainX (h4 : 4 ≤ g.x) (h1 : g.y=1) (h2 : g.z=1) :
      1 ≤ fullSupportAxisGain S g := by
    unfold fullSupportAxisGain jointAxisGain
    rw [hr,hs,ht]
    simp only [h1,h2,max_eq_right h4]
    omega
  have gainY (h4 : 4 ≤ g.y) (h1 : g.x=1) (h2 : g.z=1) :
      1 ≤ fullSupportAxisGain S g := by
    unfold fullSupportAxisGain jointAxisGain
    rw [hr,hs,ht]
    simp only [h1,h2,max_eq_right h4]
    omega
  have gainZ (h4 : 4 ≤ g.z) (h1 : g.x=1) (h2 : g.y=1) :
      1 ≤ fullSupportAxisGain S g := by
    unfold fullSupportAxisGain jointAxisGain
    rw [hr,hs,ht]
    simp only [h1,h2,max_eq_right h4]
    omega
  by_cases ha : 4 ≤ g.x
  · have hH := hHlarge (Or.inl ha)
    by_cases hb : 4 ≤ g.y
    · have hd := defect_two_large g.x g.y ha hb; omega
    by_cases hc : 4 ≤ g.z
    · have hd := defect_two_large g.x g.z ha hc; omega
    by_cases he : g.y=1 ∧ g.z=1
    · have hgain := gainX ha he.1 he.2
      have hm : max (ferrersPlaneDefect 4 g.y g.z) (rankCutPhi 4 g.y g.z)=4 := by
        rw [he.1,he.2]; exact m11
      omega
    · have hres := small_axis_resources g.y g.z hy hz (by omega) (by omega) (by omega)
      have hab := rectangle_lower 4 g.x g.y 4 g.y ha le_rfl
      have hac := rectangle_lower 4 g.x g.z 4 g.z ha le_rfl
      omega
  · by_cases hb : 4 ≤ g.y
    · have hH := hHlarge (Or.inr (Or.inl hb))
      by_cases hc : 4 ≤ g.z
      · have hd := defect_two_large g.y g.z hb hc; omega
      by_cases he : g.x=1 ∧ g.z=1
      · have hgain := gainY hb he.1 he.2
        have hm : max (ferrersPlaneDefect 4 g.x g.z) (rankCutPhi 4 g.x g.z)=4 := by
          rw [he.1,he.2]; exact m11
        omega
      · have hres := small_axis_resources g.x g.z hx hz (by omega) (by omega) (by omega)
        have hab := rectangle_lower 4 g.x g.y g.x 4 le_rfl hb
        rw [small_rect_sym g.x hx (by omega)] at hab
        have hbc := rectangle_lower 4 g.y g.z 4 g.z hb le_rfl
        omega
    · by_cases hc : 4 ≤ g.z
      · have hH := hHlarge (Or.inr (Or.inr hc))
        by_cases he : g.x=1 ∧ g.y=1
        · have hgain := gainZ hc he.1 he.2
          have hm : max (ferrersPlaneDefect 4 g.x g.y) (rankCutPhi 4 g.x g.y)=4 := by
            rw [he.1,he.2]; exact m11
          omega
        · have hres := small_axis_resources g.x g.y hx hy (by omega) (by omega) (by omega)
          have hac := rectangle_lower 4 g.x g.z g.x 4 le_rfl hc
          rw [small_rect_sym g.x hx (by omega)] at hac
          have hbc := rectangle_lower 4 g.y g.z g.y 4 le_rfl hc
          rw [small_rect_sym g.y hy (by omega)] at hbc
          omega
      · have hsmall := ferrers_weighted_four_small_triangle_lower g.x g.y g.z hx hy hz
          (by omega) (by omega) (by omega)
        omega

theorem fullSupport_t4_q444_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hr : pair12Count S.D=4) (hs : pair13Count S.D=4) (ht : pair23Count S.D=4) :
    fullTarget S ≤ S.m := by
  have h := fullSupport_q444_BF_sharp_lower S hg hf ho hr hs ht
  have hb := fullSupport_symbolic_BF_lower S hg hf ho
  have he : fullTarget S=49 := by rw [fullTarget_eq_square,hr,hs,ht]; norm_num
  omega

private theorem endpoint_H_eq_core (S : CyclicStaircase) (hr : pair12Count S.D=4)
    (hs : pair13Count S.D=4) (ht : pair23Count S.D=4) (g : Point3)
    (hshape : g=⟨4,1,1⟩ ∨ g=⟨1,4,1⟩ ∨ g=⟨1,1,4⟩) :
    fullSupportSymbolicH S g=fullCoreFinset S := by
  classical
  apply Finset.Subset.antisymm
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (mem_fullCoreFinset S p).mpr ((mem_puncturedFullCoreFinset S g p).mp hp).1
    · have hb := Finset.mem_filter.mp hp
      have hl := (mem_lowerBoxFinset g p).mp hb.1
      have hx := hl.1.1; have hy := hl.1.2.1; have hz := hl.1.2.2
      have hne : ¬ (p.x=g.x ∧ p.y=g.y ∧ p.z=g.z) := by
        rintro ⟨hx,hy,hz⟩; exact hl.2 (Point3.ext hx hy hz)
      have hfull := hb.2
      rcases hshape with rfl | rfl | rfl
      all_goals apply (mem_fullCoreFinset S p).mpr
      all_goals dsimp [FullCore]; rw [hr,hs,ht]
      all_goals dsimp at hx hy hz hne; dsimp [FullSupport] at hfull; omega
  · apply fullCore_subset_symbolic_H_of_large_coordinate S g
    rcases hshape with rfl | rfl | rfl <;> simp [hr,hs]

/-- The three isolated equality endpoints, without asserting their realizability. -/
theorem q444_axis_endpoint_exact (S : CyclicStaircase) (hr : pair12Count S.D=4)
    (hs : pair13Count S.D=4) (ht : pair23Count S.D=4) (g : Point3)
    (hshape : g=⟨4,1,1⟩ ∨ g=⟨1,4,1⟩ ∨ g=⟨1,1,4⟩) :
    fullSupportSymbolicBW S g=48 ∧ fullSupportAxisGain S g=1 ∧
      fullSupportSymbolicBF S g=49 := by
  have hH : (fullSupportSymbolicH S g).card=11 := by
    rw [endpoint_H_eq_core S hr hs ht g hshape]
    exact fullCore_q444_card S hr hs ht
  have d41 : ferrersPlaneDefect 4 4 1=1 := by decide
  have d14 : ferrersPlaneDefect 4 1 4=1 := by decide
  have d11 : ferrersPlaneDefect 4 1 1=4 := by decide
  have p41 : rankCutPhi 4 4 1=1 := by decide
  have p14 : rankCutPhi 4 1 4=1 := by decide
  have p11 : rankCutPhi 4 1 1=0 := by decide
  rcases hshape with rfl | rfl | rfl
  all_goals norm_num [fullSupportSymbolicBW,fullSupportSymbolicBF,fullSupportAxisGain,
    hr,hs,ht,hH,jointAxisGain,Nat.choose,d41,d14,d11,p41,p14,p11]

end NSP3
