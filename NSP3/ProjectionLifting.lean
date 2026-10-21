import NSP3.SupportClassification

namespace NSP3

def proj12 (p : Point3) : Point3 := ⟨p.x, p.y, 0⟩
def proj13 (p : Point3) : Point3 := ⟨p.x, 0, p.z⟩
def proj23 (p : Point3) : Point3 := ⟨0, p.y, p.z⟩

@[simp] theorem proj12_x (p : Point3) : (proj12 p).x = p.x := rfl
@[simp] theorem proj12_y (p : Point3) : (proj12 p).y = p.y := rfl
@[simp] theorem proj12_z (p : Point3) : (proj12 p).z = 0 := rfl
@[simp] theorem proj13_x (p : Point3) : (proj13 p).x = p.x := rfl
@[simp] theorem proj13_y (p : Point3) : (proj13 p).y = 0 := rfl
@[simp] theorem proj13_z (p : Point3) : (proj13 p).z = p.z := rfl
@[simp] theorem proj23_x (p : Point3) : (proj23 p).x = 0 := rfl
@[simp] theorem proj23_y (p : Point3) : (proj23 p).y = p.y := rfl
@[simp] theorem proj23_z (p : Point3) : (proj23 p).z = p.z := rfl

theorem proj12_le (p : Point3) : proj12 p ≤ p :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.zero_le _⟩

theorem proj13_le (p : Point3) : proj13 p ≤ p :=
  ⟨Nat.le_refl _, Nat.zero_le _, Nat.le_refl _⟩

theorem proj23_le (p : Point3) : proj23 p ≤ p :=
  ⟨Nat.zero_le _, Nat.le_refl _, Nat.le_refl _⟩

theorem noFull_projection_lifting (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (p : Point3)
    (_hx : 0 < p.x) (_hy : 0 < p.y) (_hz : 0 < p.z)
    (h12 : proj12 p ∈ S.D) (h13 : proj13 p ∈ S.D) (h23 : proj23 p ∈ S.D) :
    p ∈ S.D := by
  by_contra hp
  obtain ⟨b, hb, hble⟩ := exists_minimalComplement_le hp
  rcases minimalComplement_support_cases S hb with h | h | h | h | h | h | h
  · apply hb.not_mem
    apply S.down_closed.mem_of_le _ h12
    exact ⟨hble.1, hble.2.1, by simp [proj12, h.2.2]⟩
  · apply hb.not_mem
    apply S.down_closed.mem_of_le _ h12
    exact ⟨hble.1, hble.2.1, by simp [proj12, h.2.2]⟩
  · apply hb.not_mem
    apply S.down_closed.mem_of_le _ h13
    exact ⟨hble.1, by simp [proj13, h.2.1], hble.2.2⟩
  · apply hb.not_mem
    apply S.down_closed.mem_of_le _ h12
    exact ⟨hble.1, hble.2.1, by simp [proj12, h.2.2]⟩
  · apply hb.not_mem
    apply S.down_closed.mem_of_le _ h13
    exact ⟨hble.1, by simp [proj13, h.2.1], hble.2.2⟩
  · apply hb.not_mem
    apply S.down_closed.mem_of_le _ h23
    exact ⟨by simp [proj23, h.1], hble.2.1, hble.2.2⟩
  · exact (hnf.not_full hb) h

end NSP3
