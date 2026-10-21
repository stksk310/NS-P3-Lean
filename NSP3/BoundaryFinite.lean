import NSP3.SupportClassification

namespace NSP3

/-- All actual minimal-complement points, cut out of a finite predecessor cover. -/
noncomputable def minimalComplementBoundaries (S : CyclicStaircase) : Finset Point3 := by
  classical
  exact ((S.D.image fun p => p + Point3.e1) ∪
    (S.D.image fun p => p + Point3.e2) ∪
    (S.D.image fun p => p + Point3.e3)).filter (MinimalComplement S.D)

@[simp] theorem mem_minimalComplementBoundaries (S : CyclicStaircase) (b : Point3) :
    b ∈ minimalComplementBoundaries S ↔ MinimalComplement S.D b := by
  classical
  simp only [minimalComplementBoundaries, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hb
    refine ⟨?_, hb⟩
    by_cases hx : 0 < b.x
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨b.pred1, hb.pred1_mem hx, b.pred1_add_e1 hx⟩))
    · by_cases hy : 0 < b.y
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨b.pred2, hb.pred2_mem hy, b.pred2_add_e2 hy⟩))
      · have hz : 0 < b.z := by
          by_contra hn
          have hzero : b = Point3.zero := by
            ext <;> simp only [Point3.zero_x, Point3.zero_y, Point3.zero_z] <;> omega
          exact hb.not_mem (hzero ▸ S.zero_mem)
        exact Finset.mem_union_right _
          (Finset.mem_image.mpr ⟨b.pred3, hb.pred3_mem hz, b.pred3_add_e3 hz⟩)

/-- Explicit finiteness: Nat.card is never being used on an infinite boundary type. -/
theorem minimalComplement_finite (S : CyclicStaircase) :
    Finite {b : Point3 // MinimalComplement S.D b} := by
  let f : {b : Point3 // MinimalComplement S.D b} →
      {b : Point3 // b ∈ minimalComplementBoundaries S} :=
    fun b => ⟨b.1, (mem_minimalComplementBoundaries S b.1).mpr b.2⟩
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  exact congrArg (fun q : {b : Point3 // b ∈ minimalComplementBoundaries S} => q.1) h

theorem minimalComplement_card_eq_finset_card (S : CyclicStaircase) :
    Nat.card {b : Point3 // MinimalComplement S.D b} =
      (minimalComplementBoundaries S).card :=
  Nat.subtype_card _ (mem_minimalComplementBoundaries S)

end NSP3
