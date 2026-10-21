import NSP3.GeneratedSemigroupCofinite

namespace NSP3

/-- Every outside point contains a genuine immediate-predecessor border point. -/
theorem presentation_border_exists_le (D : Finset Point3) (p : Point3) (hp : p ∉ D) :
    ∃ b : Point3, MinimalComplement D b ∧ b ≤ p := by
  classical
  let size := fun q : Point3 => q.x + q.y + q.z
  have wf : WellFounded (fun u v : Point3 => size u < size v) :=
    InvImage.wf size Nat.lt_wfRel.wf
  obtain ⟨b, hb, hmin⟩ := wf.has_min {q : Point3 | q ∉ D ∧ q ≤ p} ⟨p, hp, le_rfl⟩
  refine ⟨b, ⟨hb.1, ?_, ?_, ?_⟩, hb.2⟩
  · intro hx
    by_contra hn
    have h := hmin b.pred1 ⟨hn, le_trans b.pred1_le hb.2⟩
    simp only [size, Point3.pred1_x, Point3.pred1_y, Point3.pred1_z] at h
    omega
  · intro hy
    by_contra hn
    have h := hmin b.pred2 ⟨hn, le_trans b.pred2_le hb.2⟩
    simp only [size, Point3.pred2_x, Point3.pred2_y, Point3.pred2_z] at h
    omega
  · intro hz
    by_contra hn
    have h := hmin b.pred3 ⟨hn, le_trans b.pred3_le hb.2⟩
    simp only [size, Point3.pred3_x, Point3.pred3_y, Point3.pred3_z] at h
    omega

theorem presentation_add_offset {b p : Point3} (h : b ≤ p) :
    ∃ d : Point3, b + d = p := by
  refine ⟨⟨p.x-b.x, p.y-b.y, p.z-b.z⟩, ?_⟩
  apply Point3.ext <;> simp only [Point3.add_x, Point3.add_y, Point3.add_z]
  · exact Nat.add_sub_of_le h.1
  · exact Nat.add_sub_of_le h.2.1
  · exact Nat.add_sub_of_le h.2.2

abbrev Fact4 := ℕ × Point3

/-- Actual four-input factorization map to the natural numbers. -/
def factorWeight (m a b c : ℕ) (u : Fact4) : ℕ := u.1*m + aperyWeight a b c u.2

theorem factorWeight_add (m a b c : ℕ) (u v : Fact4) :
    factorWeight m a b c (u+v) = factorWeight m a b c u + factorWeight m a b c v := by
  change (u.1+v.1)*m + aperyWeight a b c (u.2+v.2) = _
  rw [aperyWeight_add]
  unfold factorWeight
  ring

end NSP3
