import NSP3.ProjectionLifting
import NSP3.FullBoundaryAPI

namespace NSP3

/-- Actual projections, including points outside all triangular baseline cores. -/
theorem fullSupport_actual_projection_lifting (S : CyclicStaircase) {g p : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (_hp : FullSupport p) (h12 : proj12 p ∈ S.D)
    (h13 : proj13 p ∈ S.D) (h23 : proj23 p ∈ S.D)
    (havoid : ¬ g ≤ p) : p ∈ S.D := by
  by_contra hpout
  obtain ⟨b, hb, hble⟩ := exists_minimalComplement_le hpout
  rcases minimalComplement_support_cases S hb with h | h | h | h | h | h | h
  · apply hb.not_mem
    exact S.down_closed.mem_of_le (b := proj12 p)
      ⟨hble.1, hble.2.1, by simp [proj12, h.2.2]⟩ h12
  · apply hb.not_mem
    exact S.down_closed.mem_of_le (b := proj12 p)
      ⟨hble.1, hble.2.1, by simp [proj12, h.2.2]⟩ h12
  · apply hb.not_mem
    exact S.down_closed.mem_of_le (b := proj13 p)
      ⟨hble.1, by simp [proj13, h.2.1], hble.2.2⟩ h13
  · apply hb.not_mem
    exact S.down_closed.mem_of_le (b := proj12 p)
      ⟨hble.1, hble.2.1, by simp [proj12, h.2.2]⟩ h12
  · apply hb.not_mem
    exact S.down_closed.mem_of_le (b := proj13 p)
      ⟨hble.1, by simp [proj13, h.2.1], hble.2.2⟩ h13
  · apply hb.not_mem
    exact S.down_closed.mem_of_le (b := proj23 p)
      ⟨by simp [proj23, h.1], hble.2.1, hble.2.2⟩ h23
  · have heq := fullSupportBoundary_unique S hg hf hb h
    apply havoid
    rw [heq]
    exact hble

end NSP3
