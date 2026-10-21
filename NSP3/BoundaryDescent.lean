import NSP3.Boundary

namespace NSP3

private def Point3.weight (p : Point3) : ℕ := p.x + p.y + p.z

/-- Every point outside a finite set dominates an immediate-predecessor minimal outside point. -/
theorem exists_minimalComplement_le {D : Finset Point3} {x : Point3} (hx : x ∉ D) :
    ∃ b, MinimalComplement D b ∧ b ≤ x := by
  let P : ℕ → Prop := fun n =>
    ∀ y : Point3, y.weight = n → y ∉ D →
      ∃ b, MinimalComplement D b ∧ b ≤ y
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro y hyweight hy
        simp only [Point3.weight] at hyweight
        by_cases h1 : 0 < y.x → y.pred1 ∈ D
        · by_cases h2 : 0 < y.y → y.pred2 ∈ D
          · by_cases h3 : 0 < y.z → y.pred3 ∈ D
            · exact ⟨y, ⟨hy, h1, h2, h3⟩, le_rfl⟩
            · push Not at h3
              obtain ⟨hyz, hpred⟩ := h3
              have hlt : y.pred3.weight < n := by
                simp only [Point3.weight, Point3.pred3_x, Point3.pred3_y,
                  Point3.pred3_z]
                omega
              obtain ⟨b, hb, hble⟩ := ih _ hlt y.pred3 rfl hpred
              exact ⟨b, hb, hble.trans y.pred3_le⟩
          · push Not at h2
            obtain ⟨hyy, hpred⟩ := h2
            have hlt : y.pred2.weight < n := by
              simp only [Point3.weight, Point3.pred2_x, Point3.pred2_y,
                Point3.pred2_z]
              omega
            obtain ⟨b, hb, hble⟩ := ih _ hlt y.pred2 rfl hpred
            exact ⟨b, hb, hble.trans y.pred2_le⟩
        · push Not at h1
          obtain ⟨hyx, hpred⟩ := h1
          have hlt : y.pred1.weight < n := by
            simp only [Point3.weight, Point3.pred1_x, Point3.pred1_y,
              Point3.pred1_z]
            omega
          obtain ⟨b, hb, hble⟩ := ih _ hlt y.pred1 rfl hpred
          exact ⟨b, hb, hble.trans y.pred1_le⟩
  exact hP x.weight x rfl hx

/-- Distinct minimal-complement points of a down-set cannot be comparable. -/
theorem minimalComplement_not_le_of_ne {D : Finset Point3} (hD : IsDownset D)
    {b c : Point3} (hb : MinimalComplement D b) (hc : MinimalComplement D c)
    (hbc : b ≠ c) : ¬ b ≤ c := by
  intro hle
  have hstrict : b.x < c.x ∨ b.y < c.y ∨ b.z < c.z := by
    rcases hle with ⟨hx, hy, hz⟩
    by_contra h
    push Not at h
    apply hbc
    ext <;> omega
  rcases hstrict with hx | hy | hz
  · have hcx : 0 < c.x := lt_of_le_of_lt (Nat.zero_le _) hx
    have hbpred : b ≤ c.pred1 := by
      exact ⟨by simp [Point3.pred1]; omega, hle.2.1, hle.2.2⟩
    exact hb.not_mem (hD.mem_of_le hbpred (hc.pred1_mem hcx))
  · have hcy : 0 < c.y := lt_of_le_of_lt (Nat.zero_le _) hy
    have hbpred : b ≤ c.pred2 := by
      exact ⟨hle.1, by simp [Point3.pred2]; omega, hle.2.2⟩
    exact hb.not_mem (hD.mem_of_le hbpred (hc.pred2_mem hcy))
  · have hcz : 0 < c.z := lt_of_le_of_lt (Nat.zero_le _) hz
    have hbpred : b ≤ c.pred3 := by
      exact ⟨hle.1, hle.2.1, by simp [Point3.pred3]; omega⟩
    exact hb.not_mem (hD.mem_of_le hbpred (hc.pred3_mem hcz))

theorem minimalComplements_incomparable {D : Finset Point3} (hD : IsDownset D)
    {b c : Point3} (hb : MinimalComplement D b) (hc : MinimalComplement D c)
    (hbc : b ≠ c) : (¬ b ≤ c) ∧ (¬ c ≤ b) :=
  ⟨minimalComplement_not_le_of_ne hD hb hc hbc,
    minimalComplement_not_le_of_ne hD hc hb hbc.symm⟩

private theorem zero_mem_of_nonempty {D : Finset Point3} (hD : IsDownset D)
    (hne : D.Nonempty) : Point3.zero ∈ D := by
  obtain ⟨p, hp⟩ := hne
  exact hD.mem_of_le ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩ hp

/-- A nonempty finite down-set has a pure axis-1 minimal-complement point. -/
theorem exists_pure1_minimalComplement {D : Finset Point3} (hD : IsDownset D)
    (hne : D.Nonempty) :
    ∃ a, MinimalComplement D ⟨a, 0, 0⟩ ∧ Pure1 ⟨a, 0, 0⟩ := by
  classical
  let a := D.sum (fun p => p.x) + 1
  have hout : Point3.mk a 0 0 ∉ D := by
    intro ha
    have hle := Finset.single_le_sum (s := D) (f := fun p : Point3 => p.x)
      (fun _ _ => Nat.zero_le _) ha
    simp only at hle
    change a ≤ D.sum (fun p => p.x) at hle
    simp [a] at hle
  obtain ⟨b, hbmin, hble⟩ := exists_minimalComplement_le hout
  have hby : b.y = 0 := by
    have := hble.2.1
    change b.y ≤ 0 at this
    omega
  have hbz : b.z = 0 := by
    have := hble.2.2
    change b.z ≤ 0 at this
    omega
  have hzero := zero_mem_of_nonempty hD hne
  have hbxpos : 0 < b.x := by
    by_contra hnot
    have hbx : b.x = 0 := Nat.eq_zero_of_not_pos hnot
    have hbzero : b = Point3.zero := by ext <;> simp [Point3.zero, hbx, hby, hbz]
    exact hbmin.not_mem (hbzero ▸ hzero)
  refine ⟨b.x, ?_, ?_⟩
  · have hbshape : b = ⟨b.x, 0, 0⟩ := by ext <;> simp [hby, hbz]
    exact hbshape ▸ hbmin
  · exact ⟨hbxpos, rfl, rfl⟩

/-- A nonempty finite down-set has a pure axis-2 minimal-complement point. -/
theorem exists_pure2_minimalComplement {D : Finset Point3} (hD : IsDownset D)
    (hne : D.Nonempty) :
    ∃ a, MinimalComplement D ⟨0, a, 0⟩ ∧ Pure2 ⟨0, a, 0⟩ := by
  classical
  let a := D.sum (fun p => p.y) + 1
  have hout : Point3.mk 0 a 0 ∉ D := by
    intro ha
    have hle := Finset.single_le_sum (s := D) (f := fun p : Point3 => p.y)
      (fun _ _ => Nat.zero_le _) ha
    simp only at hle
    change a ≤ D.sum (fun p => p.y) at hle
    simp [a] at hle
  obtain ⟨b, hbmin, hble⟩ := exists_minimalComplement_le hout
  have hbx : b.x = 0 := by
    have := hble.1
    change b.x ≤ 0 at this
    omega
  have hbz : b.z = 0 := by
    have := hble.2.2
    change b.z ≤ 0 at this
    omega
  have hzero := zero_mem_of_nonempty hD hne
  have hbypos : 0 < b.y := by
    by_contra hnot
    have hby : b.y = 0 := Nat.eq_zero_of_not_pos hnot
    have hbzero : b = Point3.zero := by ext <;> simp [Point3.zero, hbx, hby, hbz]
    exact hbmin.not_mem (hbzero ▸ hzero)
  refine ⟨b.y, ?_, ?_⟩
  · have hbshape : b = ⟨0, b.y, 0⟩ := by ext <;> simp [hbx, hbz]
    exact hbshape ▸ hbmin
  · exact ⟨rfl, hbypos, rfl⟩

/-- A nonempty finite down-set has a pure axis-3 minimal-complement point. -/
theorem exists_pure3_minimalComplement {D : Finset Point3} (hD : IsDownset D)
    (hne : D.Nonempty) :
    ∃ a, MinimalComplement D ⟨0, 0, a⟩ ∧ Pure3 ⟨0, 0, a⟩ := by
  classical
  let a := D.sum (fun p => p.z) + 1
  have hout : Point3.mk 0 0 a ∉ D := by
    intro ha
    have hle := Finset.single_le_sum (s := D) (f := fun p : Point3 => p.z)
      (fun _ _ => Nat.zero_le _) ha
    simp only at hle
    change a ≤ D.sum (fun p => p.z) at hle
    simp [a] at hle
  obtain ⟨b, hbmin, hble⟩ := exists_minimalComplement_le hout
  have hbx : b.x = 0 := by
    have := hble.1
    change b.x ≤ 0 at this
    omega
  have hby : b.y = 0 := by
    have := hble.2.1
    change b.y ≤ 0 at this
    omega
  have hzero := zero_mem_of_nonempty hD hne
  have hbzpos : 0 < b.z := by
    by_contra hnot
    have hbz : b.z = 0 := Nat.eq_zero_of_not_pos hnot
    have hbzero : b = Point3.zero := by ext <;> simp [Point3.zero, hbx, hby, hbz]
    exact hbmin.not_mem (hbzero ▸ hzero)
  refine ⟨b.z, ?_, ?_⟩
  · have hbshape : b = ⟨0, 0, b.z⟩ := by ext <;> simp [hbx, hby]
    exact hbshape ▸ hbmin
  · exact ⟨rfl, rfl, hbzpos⟩

end NSP3
