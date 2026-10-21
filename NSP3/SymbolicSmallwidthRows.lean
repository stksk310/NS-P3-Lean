import NSP3.SymbolicTGE4Rows

namespace NSP3

/-- Disjoint yz fibers cover H, with bounds derived from H itself, not a bound on g. -/
theorem symbolic_H_card_eq_sum_rows (S : CyclicStaircase) (g : Point3) :
    (fullSupportSymbolicH S g).card =
      ∑ y ∈ Finset.Icc 1 (max g.y (pair23Count S.D)),
      ∑ z ∈ Finset.Icc 1 (max g.z (pair23Count S.D)),
        ((fullSupportSymbolicH S g).filter (fun p => p.y=y ∧ p.z=z)).card := by
  classical
  have hm : (↑(fullSupportSymbolicH S g) : Set Point3).MapsTo
      (fun p => (p.y,p.z))
      ((Finset.Icc 1 (max g.y (pair23Count S.D))).product
        (Finset.Icc 1 (max g.z (pair23Count S.D)))) := by
    intro p hp
    change (p.y,p.z) ∈ (Finset.Icc 1 (max g.y (pair23Count S.D))).product
      (Finset.Icc 1 (max g.z (pair23Count S.D)))
    simp only [Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
    rcases Finset.mem_union.mp hp with hp | hp
    · have hc := ((mem_puncturedFullCoreFinset S g p).mp hp).1
      have hy := le_max_right g.y (pair23Count S.D)
      have hz := le_max_right g.z (pair23Count S.D)
      dsimp [FullCore] at hc
      exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
    · obtain ⟨hp,hf⟩ := Finset.mem_filter.mp hp
      have hl := ((mem_lowerBoxFinset g p).mp hp).1
      have hly := hl.2.1
      have hlz := hl.2.2
      have hy := le_max_left g.y (pair23Count S.D)
      have hz := le_max_left g.z (pair23Count S.D)
      dsimp [FullSupport] at hf
      exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  have h := Finset.card_eq_sum_card_fiberwise hm
  simp only [Finset.product_eq_sprod] at h
  rw [Finset.sum_product] at h
  simpa only [Prod.mk.injEq] using h

/-- Exact core area as a sum of positive yz-row lengths, for all pair counts. -/
theorem fullCore_card_eq_sum_rows (S : CyclicStaircase) :
    (fullCoreFinset S).card =
      ∑ y ∈ Finset.Icc 1 (pair23Count S.D),
      ∑ z ∈ Finset.Icc 1 (pair23Count S.D),
        if y+z ≤ pair23Count S.D then
          min (pair12Count S.D-y) (pair13Count S.D-z) else 0 := by
  classical
  have hm : (↑(fullCoreFinset S) : Set Point3).MapsTo (fun p => (p.y,p.z))
      ((Finset.Icc 1 (pair23Count S.D)).product (Finset.Icc 1 (pair23Count S.D))) := by
    intro p hp
    have hc := (mem_fullCoreFinset S p).mp hp
    dsimp [FullCore] at hc
    change (p.y,p.z) ∈ (Finset.Icc 1 (pair23Count S.D)).product (Finset.Icc 1 (pair23Count S.D))
    simp only [Finset.product_eq_sprod,Finset.mem_product,Finset.mem_Icc]
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  have h := Finset.card_eq_sum_card_fiberwise hm
  simp only [Finset.product_eq_sprod] at h
  rw [Finset.sum_product] at h
  simp only [Prod.mk.injEq] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro z hz
  exact fullCore_positive_row_card S y z (by have := (Finset.mem_Icc.mp hy).1; omega)
    (by have := (Finset.mem_Icc.mp hz).1; omega)

end NSP3
