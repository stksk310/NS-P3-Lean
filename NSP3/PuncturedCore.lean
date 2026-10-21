import NSP3.FullBoundaryAPI

namespace NSP3

def FullBoundaryPuncturedCore (S : CyclicStaircase) (g p : Point3) : Prop :=
  FullCore S p ∧ ¬ g ≤ p

theorem fullSupport_puncturedCore_mem (S : CyclicStaircase) {g p : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hp : FullBoundaryPuncturedCore S g p) : p ∈ S.D := by
  by_contra hout
  obtain ⟨b, hb, hbp⟩ := exists_minimalComplement_le hout
  rcases minimalComplement_support_cases S hb with h | h | h | h | h | h | h
  · have hmem := pair12Triangle_subset S.down_closed hp.1.1 hp.1.2.1 hp.1.2.2.2.1
    exact hb.not_mem (S.down_closed.mem_of_le
      (show b ≤ proj12 p from ⟨hbp.1, by simp [proj12, h.2.1], by simp [proj12, h.2.2]⟩) hmem)
  · have hmem := pair12Triangle_subset S.down_closed hp.1.1 hp.1.2.1 hp.1.2.2.2.1
    exact hb.not_mem (S.down_closed.mem_of_le
      (show b ≤ proj12 p from ⟨by simp [proj12, h.1], hbp.2.1, by simp [proj12, h.2.2]⟩) hmem)
  · have hmem := pair13Triangle_subset S.down_closed hp.1.1 hp.1.2.2.1 hp.1.2.2.2.2.1
    exact hb.not_mem (S.down_closed.mem_of_le
      (show b ≤ proj13 p from ⟨by simp [proj13, h.1], by simp [proj13, h.2.1], hbp.2.2⟩) hmem)
  · have hmem := pair12Triangle_subset S.down_closed h.1 h.2.1 (by
      have := hp.1.2.2.2.1
      have hbx := hbp.1
      have hby := hbp.2.1
      omega)
    have heq : Point3.mk b.x b.y 0 = b := by ext <;> simp [h.2.2]
    exact hb.not_mem (heq ▸ hmem)
  · have hmem := pair13Triangle_subset S.down_closed h.1 h.2.2 (by
      have := hp.1.2.2.2.2.1
      have hbx := hbp.1
      have hbz := hbp.2.2
      omega)
    have heq : Point3.mk b.x 0 b.z = b := by ext <;> simp [h.2.1]
    exact hb.not_mem (heq ▸ hmem)
  · have hmem := pair23Triangle_subset S.down_closed h.2.1 h.2.2 (by
      have := hp.1.2.2.2.2.2
      have hby := hbp.2.1
      have hbz := hbp.2.2
      omega)
    have heq : Point3.mk 0 b.y b.z = b := by ext <;> simp [h.1]
    exact hb.not_mem (heq ▸ hmem)
  · have hbg := fullSupportBoundary_unique S hb h hg hfull
    exact hp.2 (hbg ▸ hbp)

end NSP3
