import NSP3.SymbolicSmallwidthStructure
import NSP3.SymbolicTGE4Residual

namespace NSP3

private def planeM (r A B : ℕ) : ℕ := max (ferrersPlaneDefect r A B) (rankCutPhi r A B)

/-- A small corner triangle, not enumeration of cyclic staircase profiles. -/
theorem ferrers_weighted_544_small_triangle_lower (A B C : ℕ)
    (ha : 1 ≤ A) (hb : 1 ≤ B) (hc : 1 ≤ C)
    (ha4 : A ≤ 4) (hb4 : B ≤ 4) (hc3 : C ≤ 3) :
    7 ≤ max (ferrersPlaneDefect 5 A B) (rankCutPhi 5 A B)+
      max (ferrersPlaneDefect 4 A C) (rankCutPhi 4 A C)+
      max (ferrersPlaneDefect 4 B C) (rankCutPhi 4 B C) := by
  interval_cases A <;> interval_cases B <;> interval_cases C <;> decide

private theorem rectangle_lower (r A B a b : ℕ) (ha : a ≤ A) (hb : b ≤ B) :
    (ferrersRectangle r a b).card ≤ planeM r A B := by
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
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _))

private theorem large_x_triangle (A B C : ℕ) (ha : 5 ≤ A)
    (hb : 1 ≤ B) (hc : 1 ≤ C) :
    6 ≤ planeM 5 A B+planeM 4 A C+planeM 4 B C := by
  by_cases hB : 4 ≤ B
  · have h := rectangle_lower 5 A B 5 4 ha hB
    have he : (ferrersRectangle 5 5 4).card=10 := by decide
    rw [he] at h; omega
  by_cases hC : 3 ≤ C
  · have h := rectangle_lower 4 A C 5 3 ha hC
    have he : (ferrersRectangle 4 5 3).card=9 := by decide
    rw [he] at h; omega
  have h1 := rectangle_lower 5 A B 5 B ha le_rfl
  have h2 := rectangle_lower 4 A C 5 C ha le_rfl
  have hsmall : 6 ≤ (ferrersRectangle 5 5 B).card+
      (ferrersRectangle 4 5 C).card+planeM 4 B C := by
    have hb3 : B ≤ 3 := by omega
    have hc2 : C ≤ 2 := by omega
    interval_cases B <;> interval_cases C <;> decide
  omega

private theorem large_y_triangle (A B C : ℕ) (ha : 1 ≤ A)
    (hb : 5 ≤ B) (hc : 1 ≤ C) :
    6 ≤ planeM 5 A B+planeM 4 A C+planeM 4 B C := by
  by_cases hA : 4 ≤ A
  · have h := rectangle_lower 5 A B 4 5 hA hb
    have he : (ferrersRectangle 5 4 5).card=10 := by decide
    rw [he] at h; omega
  by_cases hC : 3 ≤ C
  · have h := rectangle_lower 4 B C 5 3 hb hC
    have he : (ferrersRectangle 4 5 3).card=9 := by decide
    rw [he] at h; omega
  have h1 := rectangle_lower 5 A B A 5 le_rfl hb
  have h2 := rectangle_lower 4 B C 5 C hb le_rfl
  have hsmall : 6 ≤ (ferrersRectangle 5 A 5).card+
      (ferrersRectangle 4 5 C).card+planeM 4 A C := by
    have ha3 : A ≤ 3 := by omega
    have hc2 : C ≤ 2 := by omega
    interval_cases A <;> interval_cases C <;> decide
  omega

private theorem large_z_triangle (A B C : ℕ) (ha : 1 ≤ A)
    (hb : 1 ≤ B) (hc : 4 ≤ C) :
    6 ≤ planeM 5 A B+planeM 4 A C+planeM 4 B C := by
  by_cases hA : 3 ≤ A
  · have h := rectangle_lower 4 A C 3 4 hA hc
    have he : (ferrersRectangle 4 3 4).card=6 := by decide
    rw [he] at h; omega
  by_cases hB : 3 ≤ B
  · have h := rectangle_lower 4 B C 3 4 hB hc
    have he : (ferrersRectangle 4 3 4).card=6 := by decide
    rw [he] at h; omega
  have h1 := rectangle_lower 4 A C A 4 le_rfl hc
  have h2 := rectangle_lower 4 B C B 4 le_rfl hc
  have hsmall : 6 ≤ (ferrersRectangle 4 A 4).card+
      (ferrersRectangle 4 B 4).card+planeM 5 A B := by
    have ha2 : A ≤ 2 := by omega
    have hb2 : B ≤ 2 := by omega
    interval_cases A <;> interval_cases B <;> decide
  omega

/-- The q544 pilot is uniform in g; large coordinates are unbounded. -/
theorem fullSupport_q544_BF_sharp_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hr : pair12Count S.D=5) (hs : pair13Count S.D=4) (ht : pair23Count S.D=4) :
    57 ≤ fullSupportSymbolicBF S g := by
  classical
  have hx : 1 ≤ g.x := hf.1
  have hy : 1 ≤ g.y := hf.2.1
  have hz : 1 ≤ g.z := hf.2.2
  have hcore := fullCore_t4_card S (by omega) (by omega) ht
  norm_num [hr,hs] at hcore
  have hh := coreHole_card_le_largeHoleCap S hg hf ho
  have hp := card_fullCore_partition S g
  have hsub : (puncturedFullCoreFinset S g).card ≤ (fullSupportSymbolicH S g).card :=
    Finset.card_le_card (by intro p hp; exact Finset.mem_union.mpr (Or.inl hp))
  norm_num [ht,largeHoleCap] at hh
  have h12 : 12 ≤ (fullSupportSymbolicH S g).card := by omega
  have h13 (h : 5 ≤ g.x ∨ 5 ≤ g.y ∨ 4 ≤ g.z) :
      13 ≤ (fullSupportSymbolicH S g).card := by
    have hc := Finset.card_le_card (fullCore_subset_symbolic_H_of_large_coordinate S g
      (by simpa [hr,hs] using h))
    omega
  have ax := le_max_left 5 g.x
  have ay := le_max_left 5 g.y
  have az := le_max_left 5 g.z
  have hb := fullSupportSymbolicBF_eq_weighted S g
  norm_num [hr,hs,ht,Nat.choose] at hb
  by_cases hX : 5 ≤ g.x
  · have hH := h13 (Or.inl hX)
    have hw := large_x_triangle g.x g.y g.z hX hy hz
    dsimp [planeM] at hw
    omega
  by_cases hY : 5 ≤ g.y
  · have hH := h13 (Or.inr (Or.inl hY))
    have hw := large_y_triangle g.x g.y g.z hx hY hz
    dsimp [planeM] at hw
    omega
  by_cases hZ : 4 ≤ g.z
  · have hH := h13 (Or.inr (Or.inr hZ))
    have hw := large_z_triangle g.x g.y g.z hx hy hZ
    dsimp [planeM] at hw
    omega
  · have hw := ferrers_weighted_544_small_triangle_lower g.x g.y g.z hx hy hz
      (by omega) (by omega) (by omega)
    omega

theorem fullSupport_t4_q544_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hr : pair12Count S.D=5) (hs : pair13Count S.D=4) (ht : pair23Count S.D=4) :
    fullTarget S ≤ S.m := by
  have hb := fullSupport_q544_BF_sharp_lower S hg hf ho hr hs ht
  have hm := fullSupport_symbolic_BF_lower S hg hf ho
  have he : fullTarget S=57 := by rw [fullTarget_eq_square,hr,hs,ht]; norm_num
  omega

theorem fullSupport_smallwidth_refined_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : 4 ≤ pair23Count S.D) :
    fullTarget S ≤ S.m ∨ (pair12Count S.D ≤ 17 ∧
      pair12Count S.D+6 < 2*(pair13Count S.D+pair23Count S.D) ∧
      ((pair23Count S.D=4 ∧ pair13Count S.D ≤ 8) ∨
       (pair23Count S.D=5 ∧ pair13Count S.D ≤ 6) ∨
       (pair23Count S.D=6 ∧ pair13Count S.D=6)) ∧
      ¬ (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∧
      ¬ (pair12Count S.D=5 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4)) := by
  rcases fullSupport_tGE4_residual_cover S hg hf ho ht with h | h
  · exact Or.inl h
  by_cases he : pair12Count S.D=5 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4
  · exact Or.inl (fullSupport_t4_q544_symbolic_sharp S hg hf ho he.1 he.2.1 he.2.2)
  · exact Or.inr ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,he⟩

end NSP3
