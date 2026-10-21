import NSP3.BoundaryDescent

namespace NSP3

/-- The finite family of positive pair-12 minimal-complement points. -/
noncomputable def pair12Boundaries (D : Finset Point3) : Finset Point3 := by
  classical
  exact (D.image fun p => p + Point3.e1).filter fun b =>
    MinimalComplement D b ∧ Pair12 b

/-- The finite family of positive pair-13 minimal-complement points. -/
noncomputable def pair13Boundaries (D : Finset Point3) : Finset Point3 := by
  classical
  exact (D.image fun p => p + Point3.e1).filter fun b =>
    MinimalComplement D b ∧ Pair13 b

/-- The finite family of positive pair-23 minimal-complement points. -/
noncomputable def pair23Boundaries (D : Finset Point3) : Finset Point3 := by
  classical
  exact (D.image fun p => p + Point3.e2).filter fun b =>
    MinimalComplement D b ∧ Pair23 b

@[simp] theorem mem_pair12Boundaries {D : Finset Point3} {b : Point3} :
    b ∈ pair12Boundaries D ↔ MinimalComplement D b ∧ Pair12 b := by
  classical
  constructor
  · exact fun hb => (Finset.mem_filter.mp hb).2
  · intro h
    have hpred : b.pred1 ∈ D := h.1.pred1_mem h.2.1
    have heq : b.pred1 + Point3.e1 = b := b.pred1_add_e1 h.2.1
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    exact Finset.mem_image.mpr ⟨b.pred1, hpred, heq⟩

@[simp] theorem mem_pair13Boundaries {D : Finset Point3} {b : Point3} :
    b ∈ pair13Boundaries D ↔ MinimalComplement D b ∧ Pair13 b := by
  classical
  constructor
  · exact fun hb => (Finset.mem_filter.mp hb).2
  · intro h
    have hpred : b.pred1 ∈ D := h.1.pred1_mem h.2.1
    have heq : b.pred1 + Point3.e1 = b := b.pred1_add_e1 h.2.1
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    exact Finset.mem_image.mpr ⟨b.pred1, hpred, heq⟩

@[simp] theorem mem_pair23Boundaries {D : Finset Point3} {b : Point3} :
    b ∈ pair23Boundaries D ↔ MinimalComplement D b ∧ Pair23 b := by
  classical
  constructor
  · exact fun hb => (Finset.mem_filter.mp hb).2
  · intro h
    have hpred : b.pred2 ∈ D := h.1.pred2_mem h.2.2.1
    have heq : b.pred2 + Point3.e2 = b := b.pred2_add_e2 h.2.2.1
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    exact Finset.mem_image.mpr ⟨b.pred2, hpred, heq⟩

noncomputable def pair12Count (D : Finset Point3) : ℕ := (pair12Boundaries D).card
noncomputable def pair13Count (D : Finset Point3) : ℕ := (pair13Boundaries D).card
noncomputable def pair23Count (D : Finset Point3) : ℕ := (pair23Boundaries D).card

/-- Pair-12 boundaries are determined by either positive coordinate. -/
theorem pair12_eq_of_x_eq {D : Finset Point3} (hD : IsDownset D)
    {b c : Point3} (hb : b ∈ pair12Boundaries D) (hc : c ∈ pair12Boundaries D)
    (hxy : b.x = c.x) : b = c := by
  by_cases hbc : b = c
  · exact hbc
  have hbdata := mem_pair12Boundaries.mp hb
  have hcdata := mem_pair12Boundaries.mp hc
  have hinc := minimalComplements_incomparable hD hbdata.1 hcdata.1 hbc
  have hnle₁ := hinc.1
  have hnle₂ := hinc.2
  have hbz : b.z = 0 := hbdata.2.2.2
  have hcz : c.z = 0 := hcdata.2.2.2
  change ¬ (b.x ≤ c.x ∧ b.y ≤ c.y ∧ b.z ≤ c.z) at hnle₁
  change ¬ (c.x ≤ b.x ∧ c.y ≤ b.y ∧ c.z ≤ b.z) at hnle₂
  apply Point3.ext
  · exact hxy
  · omega
  · exact hbz.trans hcz.symm

theorem pair12_eq_of_y_eq {D : Finset Point3} (hD : IsDownset D)
    {b c : Point3} (hb : b ∈ pair12Boundaries D) (hc : c ∈ pair12Boundaries D)
    (hxy : b.y = c.y) : b = c := by
  by_cases hbc : b = c
  · exact hbc
  have hbdata := mem_pair12Boundaries.mp hb
  have hcdata := mem_pair12Boundaries.mp hc
  have hinc := minimalComplements_incomparable hD hbdata.1 hcdata.1 hbc
  have hnle₁ := hinc.1
  have hnle₂ := hinc.2
  have hbz : b.z = 0 := hbdata.2.2.2
  have hcz : c.z = 0 := hcdata.2.2.2
  change ¬ (b.x ≤ c.x ∧ b.y ≤ c.y ∧ b.z ≤ c.z) at hnle₁
  change ¬ (c.x ≤ b.x ∧ c.y ≤ b.y ∧ c.z ≤ b.z) at hnle₂
  apply Point3.ext
  · omega
  · exact hxy
  · exact hbz.trans hcz.symm

/-- First-coordinate order is the reverse of second-coordinate order. -/
theorem pair12_y_lt_of_x_lt {D : Finset Point3} (hD : IsDownset D)
    {b c : Point3} (hb : b ∈ pair12Boundaries D) (hc : c ∈ pair12Boundaries D)
    (hxy : b.x < c.x) : c.y < b.y := by
  have hbdata := mem_pair12Boundaries.mp hb
  have hcdata := mem_pair12Boundaries.mp hc
  have hbz : b.z = 0 := hbdata.2.2.2
  have hcz : c.z = 0 := hcdata.2.2.2
  have hbc : b ≠ c := by
    intro h
    subst c
    omega
  have hnle := (minimalComplements_incomparable hD hbdata.1 hcdata.1 hbc).1
  change ¬ (b.x ≤ c.x ∧ b.y ≤ c.y ∧ b.z ≤ c.z) at hnle
  omega

/-- The zero-based first-coordinate rank of a Pair12 boundary. -/
noncomputable def pair12Rank (D : Finset Point3) (b : Point3) : ℕ :=
  ((pair12Boundaries D).filter fun c => c.x < b.x).card

theorem pair12_rank_succ_le_x {D : Finset Point3} (hD : IsDownset D)
    {b : Point3} (hb : b ∈ pair12Boundaries D) : pair12Rank D b + 1 ≤ b.x := by
  classical
  let s := (pair12Boundaries D).filter fun c => c.x < b.x
  let t := Finset.Ico 1 b.x
  have hmaps : Set.MapsTo (fun c : Point3 => c.x) (s : Set Point3) (t : Set ℕ) := by
    intro c hc
    simp only [s, t, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hc ⊢
    exact ⟨(mem_pair12Boundaries.mp hc.1).2.1, hc.2⟩
  have hinj : Set.InjOn (fun c : Point3 => c.x) (s : Set Point3) := by
    intro c hc d hd hcd
    exact pair12_eq_of_x_eq hD (Finset.mem_filter.mp hc).1
      (Finset.mem_filter.mp hd).1 hcd
  have hcard : s.card ≤ t.card := Finset.card_le_card_of_injOn _ hmaps hinj
  have hbpos := (mem_pair12Boundaries.mp hb).2.1
  simp only [s, t, Nat.card_Ico] at hcard
  change ((pair12Boundaries D).filter fun c => c.x < b.x).card + 1 ≤ b.x
  omega

theorem pair12_count_sub_rank_le_y {D : Finset Point3} (hD : IsDownset D)
    {b : Point3} (hb : b ∈ pair12Boundaries D) :
    pair12Count D - pair12Rank D b ≤ b.y := by
  classical
  let r := (pair12Boundaries D).filter fun c => b.x ≤ c.x
  let t := Finset.Ico 1 (b.y + 1)
  have hmaps : Set.MapsTo (fun c : Point3 => c.y) (r : Set Point3) (t : Set ℕ) := by
    intro c hc
    simp only [r, t, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hc ⊢
    have hcdata := mem_pair12Boundaries.mp hc.1
    have hcy : c.y ≤ b.y := by
      rcases lt_or_eq_of_le hc.2 with hlt | heq
      · exact Nat.le_of_lt (pair12_y_lt_of_x_lt hD hb hc.1 hlt)
      · have hcb : c = b := pair12_eq_of_x_eq hD hc.1 hb heq.symm
        simp [hcb]
    exact ⟨hcdata.2.2.1, by omega⟩
  have hinj : Set.InjOn (fun c : Point3 => c.y) (r : Set Point3) := by
    intro c hc d hd hcd
    exact pair12_eq_of_y_eq hD (Finset.mem_filter.mp hc).1
      (Finset.mem_filter.mp hd).1 hcd
  have hcard : r.card ≤ t.card := Finset.card_le_card_of_injOn _ hmaps hinj
  have hpartition : pair12Rank D b + r.card = pair12Count D := by
    simpa [pair12Rank, pair12Count, r, not_lt] using
      (Finset.card_filter_add_card_filter_not (s := pair12Boundaries D)
        (fun c : Point3 => c.x < b.x))
  simp only [t, Nat.card_Ico] at hcard
  omega

theorem pair12_count_lt_coord_sum {D : Finset Point3} (hD : IsDownset D)
    {b : Point3} (hb : b ∈ pair12Boundaries D) : pair12Count D < b.x + b.y := by
  have hrank := pair12_rank_succ_le_x hD hb
  have hright := pair12_count_sub_rank_le_y hD hb
  have hrankle : pair12Rank D b ≤ pair12Count D := by
    simpa [pair12Rank, pair12Count] using
      (Finset.card_filter_le (pair12Boundaries D) (fun c : Point3 => c.x < b.x))
  omega

theorem pair12_pure1_intercept_lower {D : Finset Point3} (hD : IsDownset D)
    {b : Point3} (hb : MinimalComplement D b) (hp : Pure1 b) :
    pair12Count D + 1 ≤ b.x := by
  classical
  have hbxpos : 0 < b.x := hp.1
  have hby : b.y = 0 := hp.2.1
  have hbz : b.z = 0 := hp.2.2
  let s := pair12Boundaries D
  let t := Finset.Ico 1 b.x
  have hmaps : Set.MapsTo (fun c : Point3 => c.x) (s : Set Point3) (t : Set ℕ) := by
    intro c hc
    simp only [s, t, Finset.mem_coe, Finset.mem_Ico] at hc ⊢
    have hcdata := mem_pair12Boundaries.mp hc
    have hcxlt : c.x < b.x := by
      by_contra hnot
      have hble : b ≤ c := by
        exact ⟨Nat.le_of_not_gt hnot, hby ▸ Nat.zero_le _, hbz ▸ Nat.zero_le _⟩
      have hbc : b ≠ c := by
        intro h
        subst c
        exact (mem_pair12Boundaries.mp hc).2.2.1.ne' hby
      exact (minimalComplement_not_le_of_ne hD hb hcdata.1 hbc) hble
    exact ⟨hcdata.2.1, hcxlt⟩
  have hinj : Set.InjOn (fun c : Point3 => c.x) (s : Set Point3) := by
    intro c hc d hd hcd
    exact pair12_eq_of_x_eq hD hc hd hcd
  have hcard : s.card ≤ t.card := Finset.card_le_card_of_injOn _ hmaps hinj
  simp only [s, t, Nat.card_Ico] at hcard
  change (pair12Boundaries D).card ≤ b.x - 1 at hcard
  change (pair12Boundaries D).card + 1 ≤ b.x
  omega

theorem pair12_pure2_intercept_lower {D : Finset Point3} (hD : IsDownset D)
    {b : Point3} (hb : MinimalComplement D b) (hp : Pure2 b) :
    pair12Count D + 1 ≤ b.y := by
  classical
  have hbx : b.x = 0 := hp.1
  have hbypos : 0 < b.y := hp.2.1
  have hbz : b.z = 0 := hp.2.2
  let s := pair12Boundaries D
  let t := Finset.Ico 1 b.y
  have hmaps : Set.MapsTo (fun c : Point3 => c.y) (s : Set Point3) (t : Set ℕ) := by
    intro c hc
    simp only [s, t, Finset.mem_coe, Finset.mem_Ico] at hc ⊢
    have hcdata := mem_pair12Boundaries.mp hc
    have hcylt : c.y < b.y := by
      by_contra hnot
      have hble : b ≤ c := by
        exact ⟨hbx ▸ Nat.zero_le _, Nat.le_of_not_gt hnot, hbz ▸ Nat.zero_le _⟩
      have hbc : b ≠ c := by
        intro h
        subst c
        exact (mem_pair12Boundaries.mp hc).2.1.ne' hbx
      exact (minimalComplement_not_le_of_ne hD hb hcdata.1 hbc) hble
    exact ⟨hcdata.2.2.1, hcylt⟩
  have hinj : Set.InjOn (fun c : Point3 => c.y) (s : Set Point3) := by
    intro c hc d hd hcd
    exact pair12_eq_of_y_eq hD hc hd hcd
  have hcard : s.card ≤ t.card := Finset.card_le_card_of_injOn _ hmaps hinj
  simp only [s, t, Nat.card_Ico] at hcard
  change (pair12Boundaries D).card ≤ b.y - 1 at hcard
  change (pair12Boundaries D).card + 1 ≤ b.y
  omega

/-- The positive pair-12 Ferrers triangle is standard. -/
theorem pair12Triangle_subset {D : Finset Point3} (hD : IsDownset D)
    {x y : ℕ} (hx : 0 < x) (hy : 0 < y) (hxy : x + y ≤ pair12Count D) :
    Point3.mk x y 0 ∈ D := by
  by_contra hp
  obtain ⟨b, hbmin, hble⟩ := exists_minimalComplement_le hp
  have hbxle : b.x ≤ x := hble.1
  have hbyle : b.y ≤ y := hble.2.1
  have hbz : b.z = 0 := by
    have := hble.2.2
    simp only at this
    omega
  by_cases hbx : b.x = 0
  · by_cases hby : b.y = 0
    · have hbzero : b = Point3.zero := by
        ext <;> simp [Point3.zero, hbx, hby, hbz]
      have hqpos : 0 < pair12Count D := by omega
      have hnonempty : (pair12Boundaries D).Nonempty := by
        rw [← Finset.card_pos]
        simpa [pair12Count] using hqpos
      obtain ⟨c, hc⟩ := hnonempty
      have hcdata := mem_pair12Boundaries.mp hc
      have hpred := hcdata.1.pred1_mem hcdata.2.1
      have hzero_le : Point3.zero ≤ c.pred1 :=
        ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
      have hzero_mem : Point3.zero ∈ D := hD.mem_of_le hzero_le hpred
      exact hbmin.not_mem (hbzero ▸ hzero_mem)
    · have hbypos : 0 < b.y := Nat.pos_of_ne_zero hby
      have hlower := pair12_pure2_intercept_lower hD hbmin ⟨hbx, hbypos, hbz⟩
      omega
  · have hbxpos : 0 < b.x := Nat.pos_of_ne_zero hbx
    by_cases hby : b.y = 0
    · have hlower := pair12_pure1_intercept_lower hD hbmin ⟨hbxpos, hby, hbz⟩
      omega
    · have hbypos : 0 < b.y := Nat.pos_of_ne_zero hby
      have hbpair : b ∈ pair12Boundaries D :=
        mem_pair12Boundaries.mpr ⟨hbmin, hbxpos, hbypos, hbz⟩
      have hsum := pair12_count_lt_coord_sum hD hbpair
      omega

private theorem ferrers_card_lt_coord_sum
    {B : Finset Point3} {u v : Point3 → ℕ}
    (hupos : ∀ c ∈ B, 0 < u c) (hvpos : ∀ c ∈ B, 0 < v c)
    (huinj : Set.InjOn u (B : Set Point3))
    (horder : ∀ {c d}, c ∈ B → d ∈ B → u c < u d → v d < v c)
    {b : Point3} (hb : b ∈ B) : B.card < u b + v b := by
  classical
  let l := B.filter fun c => u c < u b
  let r := B.filter fun c => u b ≤ u c
  let tu := Finset.Ico 1 (u b)
  let tv := Finset.Ico 1 (v b + 1)
  have hlmaps : Set.MapsTo u (l : Set Point3) (tu : Set ℕ) := by
    intro c hc
    simp only [l, tu, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hc ⊢
    exact ⟨hupos c hc.1, hc.2⟩
  have hlinj : Set.InjOn u (l : Set Point3) := by
    intro c hc d hd hcd
    exact huinj (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hd).1 hcd
  have hrlmaps : Set.MapsTo v (r : Set Point3) (tv : Set ℕ) := by
    intro c hc
    simp only [r, tv, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at hc ⊢
    have hvc : v c ≤ v b := by
      rcases lt_or_eq_of_le hc.2 with hlt | heq
      · exact Nat.le_of_lt (horder hb hc.1 hlt)
      · have hcb : c = b := huinj hc.1 hb heq.symm
        simp [hcb]
    exact ⟨hvpos c hc.1, by omega⟩
  have hrinj : Set.InjOn v (r : Set Point3) := by
    intro c hc d hd hv
    by_contra hcd
    have hucd : u c ≠ u d := by
      intro hu
      exact hcd (huinj (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hd).1 hu)
    rcases lt_or_gt_of_ne hucd with hlt | hgt
    · have := horder (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hd).1 hlt
      omega
    · have := horder (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp hc).1 hgt
      omega
  have hlcard : l.card ≤ tu.card := Finset.card_le_card_of_injOn _ hlmaps hlinj
  have hrcard : r.card ≤ tv.card := Finset.card_le_card_of_injOn _ hrlmaps hrinj
  have hpartition : l.card + r.card = B.card := by
    simpa [l, r, not_lt] using
      (Finset.card_filter_add_card_filter_not (s := B) (fun c : Point3 => u c < u b))
  simp only [tu, tv, Nat.card_Ico] at hlcard hrcard
  have hubpos := hupos b hb
  omega

private theorem family_card_succ_le_of_lt
    {B : Finset Point3} {u : Point3 → ℕ} {a : ℕ}
    (hapos : 0 < a) (hupos : ∀ c ∈ B, 0 < u c)
    (huinj : Set.InjOn u (B : Set Point3))
    (hlt : ∀ c ∈ B, u c < a) : B.card + 1 ≤ a := by
  classical
  let t := Finset.Ico 1 a
  have hmaps : Set.MapsTo u (B : Set Point3) (t : Set ℕ) := by
    intro c hc
    simp only [t, Finset.mem_coe, Finset.mem_Ico]
    exact ⟨hupos c hc, hlt c hc⟩
  have hcard : B.card ≤ t.card := Finset.card_le_card_of_injOn _ hmaps huinj
  simp only [t, Nat.card_Ico] at hcard
  omega

theorem pair13_eq_of_x_eq {D : Finset Point3} (hD : IsDownset D)
    {b c : Point3} (hb : b ∈ pair13Boundaries D) (hc : c ∈ pair13Boundaries D)
    (hxy : b.x = c.x) : b = c := by
  by_cases hbc : b = c
  · exact hbc
  have hbdata := mem_pair13Boundaries.mp hb
  have hcdata := mem_pair13Boundaries.mp hc
  have hinc := minimalComplements_incomparable hD hbdata.1 hcdata.1 hbc
  have hnle₁ := hinc.1
  have hnle₂ := hinc.2
  have hby : b.y = 0 := hbdata.2.2.1
  have hcy : c.y = 0 := hcdata.2.2.1
  change ¬ (b.x ≤ c.x ∧ b.y ≤ c.y ∧ b.z ≤ c.z) at hnle₁
  change ¬ (c.x ≤ b.x ∧ c.y ≤ b.y ∧ c.z ≤ b.z) at hnle₂
  apply Point3.ext
  · exact hxy
  · exact hby.trans hcy.symm
  · omega

theorem pair13_eq_of_z_eq {D : Finset Point3} (hD : IsDownset D)
    {b c : Point3} (hb : b ∈ pair13Boundaries D) (hc : c ∈ pair13Boundaries D)
    (hz : b.z = c.z) : b = c := by
  by_cases hbc : b = c
  · exact hbc
  have hbdata := mem_pair13Boundaries.mp hb
  have hcdata := mem_pair13Boundaries.mp hc
  have hinc := minimalComplements_incomparable hD hbdata.1 hcdata.1 hbc
  have hnle₁ := hinc.1
  have hnle₂ := hinc.2
  have hby : b.y = 0 := hbdata.2.2.1
  have hcy : c.y = 0 := hcdata.2.2.1
  change ¬ (b.x ≤ c.x ∧ b.y ≤ c.y ∧ b.z ≤ c.z) at hnle₁
  change ¬ (c.x ≤ b.x ∧ c.y ≤ b.y ∧ c.z ≤ b.z) at hnle₂
  apply Point3.ext
  · omega
  · exact hby.trans hcy.symm
  · exact hz

theorem pair13_z_lt_of_x_lt {D : Finset Point3} (hD : IsDownset D)
    {b c : Point3} (hb : b ∈ pair13Boundaries D) (hc : c ∈ pair13Boundaries D)
    (hx : b.x < c.x) : c.z < b.z := by
  have hbdata := mem_pair13Boundaries.mp hb
  have hcdata := mem_pair13Boundaries.mp hc
  have hbc : b ≠ c := by intro h; subst c; omega
  have hnle := (minimalComplements_incomparable hD hbdata.1 hcdata.1 hbc).1
  have hby : b.y = 0 := hbdata.2.2.1
  have hcy : c.y = 0 := hcdata.2.2.1
  change ¬ (b.x ≤ c.x ∧ b.y ≤ c.y ∧ b.z ≤ c.z) at hnle
  omega

theorem pair13_count_lt_coord_sum {D : Finset Point3} (hD : IsDownset D)
    {b : Point3} (hb : b ∈ pair13Boundaries D) : pair13Count D < b.x + b.z := by
  change (pair13Boundaries D).card < b.x + b.z
  exact ferrers_card_lt_coord_sum
    (fun c hc => (mem_pair13Boundaries.mp hc).2.1)
    (fun c hc => (mem_pair13Boundaries.mp hc).2.2.2)
    (fun _ hc _ hd h => pair13_eq_of_x_eq hD hc hd h)
    (fun hc hd h => pair13_z_lt_of_x_lt hD hc hd h) hb

theorem pair23_eq_of_y_eq {D : Finset Point3} (hD : IsDownset D)
    {b c : Point3} (hb : b ∈ pair23Boundaries D) (hc : c ∈ pair23Boundaries D)
    (hy : b.y = c.y) : b = c := by
  by_cases hbc : b = c
  · exact hbc
  have hbdata := mem_pair23Boundaries.mp hb
  have hcdata := mem_pair23Boundaries.mp hc
  have hinc := minimalComplements_incomparable hD hbdata.1 hcdata.1 hbc
  have hnle₁ := hinc.1
  have hnle₂ := hinc.2
  have hbx : b.x = 0 := hbdata.2.1
  have hcx : c.x = 0 := hcdata.2.1
  change ¬ (b.x ≤ c.x ∧ b.y ≤ c.y ∧ b.z ≤ c.z) at hnle₁
  change ¬ (c.x ≤ b.x ∧ c.y ≤ b.y ∧ c.z ≤ b.z) at hnle₂
  apply Point3.ext
  · exact hbx.trans hcx.symm
  · exact hy
  · omega

theorem pair23_eq_of_z_eq {D : Finset Point3} (hD : IsDownset D)
    {b c : Point3} (hb : b ∈ pair23Boundaries D) (hc : c ∈ pair23Boundaries D)
    (hz : b.z = c.z) : b = c := by
  by_cases hbc : b = c
  · exact hbc
  have hbdata := mem_pair23Boundaries.mp hb
  have hcdata := mem_pair23Boundaries.mp hc
  have hinc := minimalComplements_incomparable hD hbdata.1 hcdata.1 hbc
  have hnle₁ := hinc.1
  have hnle₂ := hinc.2
  have hbx : b.x = 0 := hbdata.2.1
  have hcx : c.x = 0 := hcdata.2.1
  change ¬ (b.x ≤ c.x ∧ b.y ≤ c.y ∧ b.z ≤ c.z) at hnle₁
  change ¬ (c.x ≤ b.x ∧ c.y ≤ b.y ∧ c.z ≤ b.z) at hnle₂
  apply Point3.ext
  · exact hbx.trans hcx.symm
  · omega
  · exact hz

theorem pair23_z_lt_of_y_lt {D : Finset Point3} (hD : IsDownset D)
    {b c : Point3} (hb : b ∈ pair23Boundaries D) (hc : c ∈ pair23Boundaries D)
    (hy : b.y < c.y) : c.z < b.z := by
  have hbdata := mem_pair23Boundaries.mp hb
  have hcdata := mem_pair23Boundaries.mp hc
  have hbc : b ≠ c := by intro h; subst c; omega
  have hnle := (minimalComplements_incomparable hD hbdata.1 hcdata.1 hbc).1
  have hbx : b.x = 0 := hbdata.2.1
  have hcx : c.x = 0 := hcdata.2.1
  change ¬ (b.x ≤ c.x ∧ b.y ≤ c.y ∧ b.z ≤ c.z) at hnle
  omega

theorem pair23_count_lt_coord_sum {D : Finset Point3} (hD : IsDownset D)
    {b : Point3} (hb : b ∈ pair23Boundaries D) : pair23Count D < b.y + b.z := by
  change (pair23Boundaries D).card < b.y + b.z
  exact ferrers_card_lt_coord_sum
    (fun c hc => (mem_pair23Boundaries.mp hc).2.2.1)
    (fun c hc => (mem_pair23Boundaries.mp hc).2.2.2)
    (fun _ hc _ hd h => pair23_eq_of_y_eq hD hc hd h)
    (fun hc hd h => pair23_z_lt_of_y_lt hD hc hd h) hb

theorem pair13_pure1_intercept_lower {D : Finset Point3} (hD : IsDownset D)
    {b : Point3} (hb : MinimalComplement D b) (hp : Pure1 b) :
    pair13Count D + 1 ≤ b.x := by
  change (pair13Boundaries D).card + 1 ≤ b.x
  apply family_card_succ_le_of_lt hp.1
  · exact fun c hc => (mem_pair13Boundaries.mp hc).2.1
  · exact fun _ hc _ hd h => pair13_eq_of_x_eq hD hc hd h
  · intro c hc
    have hcdata := mem_pair13Boundaries.mp hc
    by_contra hnot
    have hle : b ≤ c := by
      exact ⟨Nat.le_of_not_gt hnot, hp.2.1 ▸ Nat.zero_le _, hp.2.2 ▸ Nat.zero_le _⟩
    have hne : b ≠ c := by
      intro h
      subst c
      exact hcdata.2.2.2.ne' hp.2.2
    exact (minimalComplement_not_le_of_ne hD hb hcdata.1 hne) hle

theorem pair13_pure3_intercept_lower {D : Finset Point3} (hD : IsDownset D)
    {b : Point3} (hb : MinimalComplement D b) (hp : Pure3 b) :
    pair13Count D + 1 ≤ b.z := by
  change (pair13Boundaries D).card + 1 ≤ b.z
  apply family_card_succ_le_of_lt hp.2.2
  · exact fun c hc => (mem_pair13Boundaries.mp hc).2.2.2
  · exact fun _ hc _ hd h => pair13_eq_of_z_eq hD hc hd h
  · intro c hc
    have hcdata := mem_pair13Boundaries.mp hc
    by_contra hnot
    have hle : b ≤ c := by
      exact ⟨hp.1 ▸ Nat.zero_le _, hp.2.1 ▸ Nat.zero_le _, Nat.le_of_not_gt hnot⟩
    have hne : b ≠ c := by
      intro h
      subst c
      exact hcdata.2.1.ne' hp.1
    exact (minimalComplement_not_le_of_ne hD hb hcdata.1 hne) hle

theorem pair23_pure2_intercept_lower {D : Finset Point3} (hD : IsDownset D)
    {b : Point3} (hb : MinimalComplement D b) (hp : Pure2 b) :
    pair23Count D + 1 ≤ b.y := by
  change (pair23Boundaries D).card + 1 ≤ b.y
  apply family_card_succ_le_of_lt hp.2.1
  · exact fun c hc => (mem_pair23Boundaries.mp hc).2.2.1
  · exact fun _ hc _ hd h => pair23_eq_of_y_eq hD hc hd h
  · intro c hc
    have hcdata := mem_pair23Boundaries.mp hc
    by_contra hnot
    have hle : b ≤ c := by
      exact ⟨hp.1 ▸ Nat.zero_le _, Nat.le_of_not_gt hnot, hp.2.2 ▸ Nat.zero_le _⟩
    have hne : b ≠ c := by
      intro h
      subst c
      exact hcdata.2.2.2.ne' hp.2.2
    exact (minimalComplement_not_le_of_ne hD hb hcdata.1 hne) hle

theorem pair23_pure3_intercept_lower {D : Finset Point3} (hD : IsDownset D)
    {b : Point3} (hb : MinimalComplement D b) (hp : Pure3 b) :
    pair23Count D + 1 ≤ b.z := by
  change (pair23Boundaries D).card + 1 ≤ b.z
  apply family_card_succ_le_of_lt hp.2.2
  · exact fun c hc => (mem_pair23Boundaries.mp hc).2.2.2
  · exact fun _ hc _ hd h => pair23_eq_of_z_eq hD hc hd h
  · intro c hc
    have hcdata := mem_pair23Boundaries.mp hc
    by_contra hnot
    have hle : b ≤ c := by
      exact ⟨hp.1 ▸ Nat.zero_le _, hp.2.1 ▸ Nat.zero_le _, Nat.le_of_not_gt hnot⟩
    have hne : b ≠ c := by
      intro h
      subst c
      exact hcdata.2.2.1.ne' hp.2.1
    exact (minimalComplement_not_le_of_ne hD hb hcdata.1 hne) hle

/-- The positive pair-13 Ferrers triangle is standard. -/
theorem pair13Triangle_subset {D : Finset Point3} (hD : IsDownset D)
    {x z : ℕ} (hx : 0 < x) (_hz : 0 < z) (hxz : x + z ≤ pair13Count D) :
    Point3.mk x 0 z ∈ D := by
  by_contra hp
  obtain ⟨b, hbmin, hble⟩ := exists_minimalComplement_le hp
  have hbxle : b.x ≤ x := hble.1
  have hbyle0 : b.y ≤ 0 := hble.2.1
  have hbzle : b.z ≤ z := hble.2.2
  have hby : b.y = 0 := by omega
  by_cases hbx : b.x = 0
  · by_cases hbz : b.z = 0
    · have hbzero : b = Point3.zero := by
        ext <;> simp [Point3.zero, hbx, hby, hbz]
      have hqpos : 0 < pair13Count D := by omega
      have hnonempty : (pair13Boundaries D).Nonempty := by
        rw [← Finset.card_pos]
        simpa [pair13Count] using hqpos
      obtain ⟨c, hc⟩ := hnonempty
      have hcdata := mem_pair13Boundaries.mp hc
      have hpred := hcdata.1.pred1_mem hcdata.2.1
      have hzero_mem := hD.mem_of_le
        (show Point3.zero ≤ c.pred1 from ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩) hpred
      exact hbmin.not_mem (hbzero ▸ hzero_mem)
    · have hbzpos : 0 < b.z := Nat.pos_of_ne_zero hbz
      have hlower := pair13_pure3_intercept_lower hD hbmin ⟨hbx, hby, hbzpos⟩
      omega
  · have hbxpos : 0 < b.x := Nat.pos_of_ne_zero hbx
    by_cases hbz : b.z = 0
    · have hlower := pair13_pure1_intercept_lower hD hbmin ⟨hbxpos, hby, hbz⟩
      omega
    · have hbzpos : 0 < b.z := Nat.pos_of_ne_zero hbz
      have hbpair : b ∈ pair13Boundaries D :=
        mem_pair13Boundaries.mpr ⟨hbmin, hbxpos, hby, hbzpos⟩
      have hsum := pair13_count_lt_coord_sum hD hbpair
      omega

/-- The positive pair-23 Ferrers triangle is standard. -/
theorem pair23Triangle_subset {D : Finset Point3} (hD : IsDownset D)
    {y z : ℕ} (hy : 0 < y) (_hz : 0 < z) (hyz : y + z ≤ pair23Count D) :
    Point3.mk 0 y z ∈ D := by
  by_contra hp
  obtain ⟨b, hbmin, hble⟩ := exists_minimalComplement_le hp
  have hbxle0 : b.x ≤ 0 := hble.1
  have hbyle : b.y ≤ y := hble.2.1
  have hbzle : b.z ≤ z := hble.2.2
  have hbx : b.x = 0 := by omega
  by_cases hby : b.y = 0
  · by_cases hbz : b.z = 0
    · have hbzero : b = Point3.zero := by
        ext <;> simp [Point3.zero, hbx, hby, hbz]
      have hqpos : 0 < pair23Count D := by omega
      have hnonempty : (pair23Boundaries D).Nonempty := by
        rw [← Finset.card_pos]
        simpa [pair23Count] using hqpos
      obtain ⟨c, hc⟩ := hnonempty
      have hcdata := mem_pair23Boundaries.mp hc
      have hpred := hcdata.1.pred2_mem hcdata.2.2.1
      have hzero_mem := hD.mem_of_le
        (show Point3.zero ≤ c.pred2 from ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩) hpred
      exact hbmin.not_mem (hbzero ▸ hzero_mem)
    · have hbzpos : 0 < b.z := Nat.pos_of_ne_zero hbz
      have hlower := pair23_pure3_intercept_lower hD hbmin ⟨hbx, hby, hbzpos⟩
      omega
  · have hbypos : 0 < b.y := Nat.pos_of_ne_zero hby
    by_cases hbz : b.z = 0
    · have hlower := pair23_pure2_intercept_lower hD hbmin ⟨hbx, hbypos, hbz⟩
      omega
    · have hbzpos : 0 < b.z := Nat.pos_of_ne_zero hbz
      have hbpair : b ∈ pair23Boundaries D :=
        mem_pair23Boundaries.mpr ⟨hbmin, hbx, hbypos, hbzpos⟩
      have hsum := pair23_count_lt_coord_sum hD hbpair
      omega

end NSP3
