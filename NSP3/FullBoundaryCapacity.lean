import NSP3.FullBoundaryAPI

namespace NSP3

private theorem pair12_terminal_bounds (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (b : Pair12Boundary S) (hx : g.x ≤ b.1.x) (hy : g.y ≤ b.1.y) :
    pure3Intercept S - g.z ≤ pair12ReturnCoord S b ∧
      pair12ReturnCoord S b < pure3Intercept S := by
  let z : Point3 := ⟨b.1.x - g.x, b.1.y - g.y, 0⟩
  have hzle : z ≤ b.1 := by
    exact ⟨Nat.sub_le _ _, Nat.sub_le _ _, by simp [z, b.2.2.2]⟩
  have hzmem : z ∈ S.D := by
    by_contra hzout
    obtain ⟨a, ha, haz⟩ := exists_minimalComplement_le hzout
    have hab : a ≤ b.1 := le_trans haz hzle
    by_cases habEq : a = b.1
    · subst a
      have hxz := haz.1
      change b.1.x ≤ b.1.x - g.x at hxz
      have := hfull.1
      omega
    · exact (minimalComplements_incomparable S.down_closed ha b.2.1 habEq).1 hab
  let c := pair12ReturnCoord S b
  have hrho : S.rho b.1 = Point3.mk 0 0 c := by
    apply Point3.ext
    · exact complementFaceReturn₁ S b.2.1 b.2.2.1
    · exact complementFaceReturn₂ S b.2.1 b.2.2.2.1
    · rfl
  have hcstd : Point3.mk 0 0 c ∈ S.D := by rw [← hrho]; exact S.rho_mem _
  have hcupper : c < pure3Intercept S := (pure3_axis_mem_iff S c).mp hcstd
  have hzg : z + g = b.1 + Point3.mk 0 0 g.z := by
    apply Point3.ext
    · simp [z, Nat.sub_add_cancel hx]
    · simp [z, Nat.sub_add_cancel hy]
    · simp [z, b.2.2.2]
  have hresg : S.residue g = 0 := by
    rw [← S.residue_rho g, fullSupportBoundary_return_zero S hg hfull]
    exact S.residue_zero
  have hresb : S.residue b.1 = S.residue (Point3.mk 0 0 c) := by
    rw [← S.residue_rho b.1, hrho]
  have hres : S.residue z = S.residue (Point3.mk 0 0 (c + g.z)) := by
    calc
      S.residue z = S.residue z + 0 := by simp
      _ = S.residue z + S.residue g := by rw [hresg]
      _ = S.residue (z + g) := (S.residue_add z g).symm
      _ = S.residue (b.1 + Point3.mk 0 0 g.z) := by rw [hzg]
      _ = S.residue b.1 + S.residue (Point3.mk 0 0 g.z) := S.residue_add _ _
      _ = S.residue (Point3.mk 0 0 c) + S.residue (Point3.mk 0 0 g.z) := by rw [hresb]
      _ = S.residue (Point3.mk 0 0 c + Point3.mk 0 0 g.z) :=
        (S.residue_add _ _).symm
      _ = S.residue (Point3.mk 0 0 (c + g.z)) := by congr 1
  have haxisOut : Point3.mk 0 0 (c + g.z) ∉ S.D := by
    intro haxis
    have heq := S.standard_eq_of_residue_eq hzmem haxis hres
    have hgz := hfull.2.2
    have := congrArg Point3.z heq
    simp [z] at this
    omega
  have hclower : pure3Intercept S ≤ c + g.z := by
    by_contra h
    exact haxisOut ((pure3_axis_mem_iff S _).mpr (by omega))
  exact ⟨by omega, hcupper⟩

theorem pair12_terminal_return_capacity (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    pair12Count S.D ≤ g.x + g.y + g.z - 2 := by
  classical
  let A := Fin (g.x - 1)
  let B := Fin (g.y - 1)
  let C := Fin g.z
  let f : Pair12Boundary S → A ⊕ (B ⊕ C) := fun b =>
    if hx : b.1.x < g.x then
      Sum.inl ⟨b.1.x - 1, by have := b.2.2.1; omega⟩
    else if hy : b.1.y < g.y then
      Sum.inr (Sum.inl ⟨b.1.y - 1, by have := b.2.2.2.1; omega⟩)
    else
      Sum.inr (Sum.inr ⟨pair12ReturnCoord S b - (pure3Intercept S - g.z), by
        have hb := pair12_terminal_bounds S hg hfull b (by omega) (by omega)
        omega⟩)
  have hf : Function.Injective f := by
    intro b d hbd
    by_cases hbx : b.1.x < g.x
    · by_cases hdx : d.1.x < g.x
      · simp only [f, dif_pos hbx, dif_pos hdx] at hbd
        apply Subtype.ext
        apply pair12_eq_of_x_eq S.down_closed (mem_pair12Boundaries.mpr b.2)
          (mem_pair12Boundaries.mpr d.2)
        have hbpos := b.2.2.1; have hdpos := d.2.2.1
        have hv := congrArg (fun x => x.val) (Sum.inl_injective hbd)
        simp at hv
        omega
      · simp only [f, dif_pos hbx, dif_neg hdx] at hbd
        split at hbd <;> contradiction
    · by_cases hdx : d.1.x < g.x
      · simp only [f, dif_neg hbx, dif_pos hdx] at hbd
        split at hbd <;> contradiction
      · by_cases hby : b.1.y < g.y
        · by_cases hdy : d.1.y < g.y
          · simp only [f, dif_neg hbx, dif_neg hdx, dif_pos hby, dif_pos hdy] at hbd
            apply Subtype.ext
            apply pair12_eq_of_y_eq S.down_closed (mem_pair12Boundaries.mpr b.2)
              (mem_pair12Boundaries.mpr d.2)
            have hbpos := b.2.2.2.1; have hdpos := d.2.2.2.1
            have hv := congrArg (fun x => x.val)
              (Sum.inl_injective (Sum.inr_injective hbd))
            simp at hv
            omega
          · simp [f, hbx, hdx, hby, hdy] at hbd
        · by_cases hdy : d.1.y < g.y
          · simp [f, hbx, hdx, hby, hdy] at hbd
          · simp only [f, dif_neg hbx, dif_neg hdx, dif_neg hby, dif_neg hdy] at hbd
            apply pair12ReturnCoord_injective S
            have hb := pair12_terminal_bounds S hg hfull b (by omega) (by omega)
            have hd := pair12_terminal_bounds S hg hfull d (by omega) (by omega)
            have hv := congrArg (fun x => x.val)
              (Sum.inr_injective (Sum.inr_injective hbd))
            simp at hv
            omega
  have hcard := Fintype.card_le_of_injective f hf
  simp only [card_pair12Boundary, Fintype.card_sum, Fintype.card_fin, A, B, C] at hcard
  have hx := hfull.1
  have hy := hfull.2.1
  omega

private theorem pair13_terminal_bounds (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (b : Pair13Boundary S) (hx : g.x ≤ b.1.x) (hz : g.z ≤ b.1.z) :
    pure2Intercept S - g.y ≤ pair13ReturnCoord S b ∧
      pair13ReturnCoord S b < pure2Intercept S := by
  let w : Point3 := ⟨b.1.x - g.x, 0, b.1.z - g.z⟩
  have hwle : w ≤ b.1 := ⟨Nat.sub_le _ _, by simp [w, b.2.2.2.1], Nat.sub_le _ _⟩
  have hwmem : w ∈ S.D := by
    by_contra hwout
    obtain ⟨a, ha, haw⟩ := exists_minimalComplement_le hwout
    have hab : a ≤ b.1 := le_trans haw hwle
    by_cases heq : a = b.1
    · subst a
      have hxw := haw.1
      change b.1.x ≤ b.1.x - g.x at hxw
      have := hfull.1
      omega
    · exact (minimalComplements_incomparable S.down_closed ha b.2.1 heq).1 hab
  let c := pair13ReturnCoord S b
  have hrho : S.rho b.1 = Point3.mk 0 c 0 := by
    apply Point3.ext
    · exact complementFaceReturn₁ S b.2.1 b.2.2.1
    · rfl
    · exact complementFaceReturn₃ S b.2.1 b.2.2.2.2
  have hcstd : Point3.mk 0 c 0 ∈ S.D := by rw [← hrho]; exact S.rho_mem _
  have hcupper : c < pure2Intercept S := (pure2_axis_mem_iff S c).mp hcstd
  have hwg : w + g = b.1 + Point3.mk 0 g.y 0 := by
    apply Point3.ext
    · simp [w, Nat.sub_add_cancel hx]
    · simp [w, b.2.2.2.1]
    · simp [w, Nat.sub_add_cancel hz]
  have hresg : S.residue g = 0 := by
    rw [← S.residue_rho g, fullSupportBoundary_return_zero S hg hfull]
    exact S.residue_zero
  have hresb : S.residue b.1 = S.residue (Point3.mk 0 c 0) := by
    rw [← S.residue_rho b.1, hrho]
  have hres : S.residue w = S.residue (Point3.mk 0 (c + g.y) 0) := by
    calc
      S.residue w = S.residue w + 0 := by simp
      _ = S.residue w + S.residue g := by rw [hresg]
      _ = S.residue (w + g) := (S.residue_add w g).symm
      _ = S.residue (b.1 + Point3.mk 0 g.y 0) := by rw [hwg]
      _ = S.residue b.1 + S.residue (Point3.mk 0 g.y 0) := S.residue_add _ _
      _ = S.residue (Point3.mk 0 c 0) + S.residue (Point3.mk 0 g.y 0) := by rw [hresb]
      _ = S.residue (Point3.mk 0 c 0 + Point3.mk 0 g.y 0) := (S.residue_add _ _).symm
      _ = S.residue (Point3.mk 0 (c + g.y) 0) := by congr 1
  have haxisOut : Point3.mk 0 (c + g.y) 0 ∉ S.D := by
    intro haxis
    have heq := S.standard_eq_of_residue_eq hwmem haxis hres
    have hgy := hfull.2.1
    have := congrArg Point3.y heq
    simp [w] at this
    omega
  have hclower : pure2Intercept S ≤ c + g.y := by
    by_contra h
    exact haxisOut ((pure2_axis_mem_iff S _).mpr (by omega))
  exact ⟨by omega, hcupper⟩

theorem pair13_terminal_return_capacity (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    pair13Count S.D ≤ g.x + g.y + g.z - 2 := by
  classical
  let f : Pair13Boundary S → Fin (g.x - 1) ⊕ (Fin (g.z - 1) ⊕ Fin g.y) := fun b =>
    if hx : b.1.x < g.x then Sum.inl ⟨b.1.x - 1, by have := b.2.2.1; omega⟩
    else if hz : b.1.z < g.z then
      Sum.inr (Sum.inl ⟨b.1.z - 1, by have := b.2.2.2.2; omega⟩)
    else Sum.inr (Sum.inr
      ⟨pair13ReturnCoord S b - (pure2Intercept S - g.y), by
        have hb := pair13_terminal_bounds S hg hfull b (by omega) (by omega); omega⟩)
  have hf : Function.Injective f := by
    intro b d hbd
    by_cases hbx : b.1.x < g.x
    · by_cases hdx : d.1.x < g.x
      · simp only [f, dif_pos hbx, dif_pos hdx] at hbd
        apply Subtype.ext
        apply pair13_eq_of_x_eq S.down_closed (mem_pair13Boundaries.mpr b.2)
          (mem_pair13Boundaries.mpr d.2)
        have bp := b.2.2.1; have dp := d.2.2.1
        have hv := congrArg (fun x => x.val) (Sum.inl_injective hbd)
        simp at hv; omega
      · simp only [f, dif_pos hbx, dif_neg hdx] at hbd; split at hbd <;> contradiction
    · by_cases hdx : d.1.x < g.x
      · simp only [f, dif_neg hbx, dif_pos hdx] at hbd; split at hbd <;> contradiction
      · by_cases hbz : b.1.z < g.z
        · by_cases hdz : d.1.z < g.z
          · simp only [f, dif_neg hbx, dif_neg hdx, dif_pos hbz, dif_pos hdz] at hbd
            apply Subtype.ext
            apply pair13_eq_of_z_eq S.down_closed (mem_pair13Boundaries.mpr b.2)
              (mem_pair13Boundaries.mpr d.2)
            have bp := b.2.2.2.2; have dp := d.2.2.2.2
            have hv := congrArg (fun x => x.val)
              (Sum.inl_injective (Sum.inr_injective hbd))
            simp at hv; omega
          · simp [f, hbx, hdx, hbz, hdz] at hbd
        · by_cases hdz : d.1.z < g.z
          · simp [f, hbx, hdx, hbz, hdz] at hbd
          · simp only [f, dif_neg hbx, dif_neg hdx, dif_neg hbz, dif_neg hdz] at hbd
            apply pair13ReturnCoord_injective S
            have hb := pair13_terminal_bounds S hg hfull b (by omega) (by omega)
            have hd := pair13_terminal_bounds S hg hfull d (by omega) (by omega)
            have hv := congrArg (fun x => x.val)
              (Sum.inr_injective (Sum.inr_injective hbd))
            simp at hv; omega
  have hcard := Fintype.card_le_of_injective f hf
  simp only [card_pair13Boundary, Fintype.card_sum, Fintype.card_fin] at hcard
  have hx := hfull.1; have hy := hfull.2.1; have hz := hfull.2.2
  omega

private theorem pair23_terminal_bounds (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (b : Pair23Boundary S) (hy : g.y ≤ b.1.y) (hz : g.z ≤ b.1.z) :
    pure1Intercept S - g.x ≤ pair23ReturnCoord S b ∧
      pair23ReturnCoord S b < pure1Intercept S := by
  let w : Point3 := ⟨0, b.1.y - g.y, b.1.z - g.z⟩
  have hwle : w ≤ b.1 := ⟨by simp [w, b.2.2.1], Nat.sub_le _ _, Nat.sub_le _ _⟩
  have hwmem : w ∈ S.D := by
    by_contra hwout
    obtain ⟨a, ha, haw⟩ := exists_minimalComplement_le hwout
    have hab : a ≤ b.1 := le_trans haw hwle
    by_cases heq : a = b.1
    · subst a
      have hyw := haw.2.1
      change b.1.y ≤ b.1.y - g.y at hyw
      have := hfull.2.1
      omega
    · exact (minimalComplements_incomparable S.down_closed ha b.2.1 heq).1 hab
  let c := pair23ReturnCoord S b
  have hrho : S.rho b.1 = Point3.mk c 0 0 := by
    apply Point3.ext
    · rfl
    · exact complementFaceReturn₂ S b.2.1 b.2.2.2.1
    · exact complementFaceReturn₃ S b.2.1 b.2.2.2.2
  have hcstd : Point3.mk c 0 0 ∈ S.D := by rw [← hrho]; exact S.rho_mem _
  have hcupper : c < pure1Intercept S := (pure1_axis_mem_iff S c).mp hcstd
  have hwg : w + g = b.1 + Point3.mk g.x 0 0 := by
    apply Point3.ext
    · simp [w, b.2.2.1]
    · simp [w, Nat.sub_add_cancel hy]
    · simp [w, Nat.sub_add_cancel hz]
  have hresg : S.residue g = 0 := by
    rw [← S.residue_rho g, fullSupportBoundary_return_zero S hg hfull]
    exact S.residue_zero
  have hresb : S.residue b.1 = S.residue (Point3.mk c 0 0) := by
    rw [← S.residue_rho b.1, hrho]
  have hres : S.residue w = S.residue (Point3.mk (c + g.x) 0 0) := by
    calc
      S.residue w = S.residue w + 0 := by simp
      _ = S.residue w + S.residue g := by rw [hresg]
      _ = S.residue (w + g) := (S.residue_add w g).symm
      _ = S.residue (b.1 + Point3.mk g.x 0 0) := by rw [hwg]
      _ = S.residue b.1 + S.residue (Point3.mk g.x 0 0) := S.residue_add _ _
      _ = S.residue (Point3.mk c 0 0) + S.residue (Point3.mk g.x 0 0) := by rw [hresb]
      _ = S.residue (Point3.mk c 0 0 + Point3.mk g.x 0 0) := (S.residue_add _ _).symm
      _ = S.residue (Point3.mk (c + g.x) 0 0) := by congr 1
  have haxisOut : Point3.mk (c + g.x) 0 0 ∉ S.D := by
    intro haxis
    have heq := S.standard_eq_of_residue_eq hwmem haxis hres
    have hgx := hfull.1
    have := congrArg Point3.x heq
    simp [w] at this
    omega
  have hclower : pure1Intercept S ≤ c + g.x := by
    by_contra h
    exact haxisOut ((pure1_axis_mem_iff S _).mpr (by omega))
  exact ⟨by omega, hcupper⟩

theorem pair23_terminal_return_capacity (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    pair23Count S.D ≤ g.x + g.y + g.z - 2 := by
  classical
  let f : Pair23Boundary S → Fin (g.y - 1) ⊕ (Fin (g.z - 1) ⊕ Fin g.x) := fun b =>
    if hy : b.1.y < g.y then Sum.inl ⟨b.1.y - 1, by have := b.2.2.2.1; omega⟩
    else if hz : b.1.z < g.z then
      Sum.inr (Sum.inl ⟨b.1.z - 1, by have := b.2.2.2.2; omega⟩)
    else Sum.inr (Sum.inr
      ⟨pair23ReturnCoord S b - (pure1Intercept S - g.x), by
        have hb := pair23_terminal_bounds S hg hfull b (by omega) (by omega); omega⟩)
  have hf : Function.Injective f := by
    intro b d hbd
    by_cases hby : b.1.y < g.y
    · by_cases hdy : d.1.y < g.y
      · simp only [f, dif_pos hby, dif_pos hdy] at hbd
        apply Subtype.ext
        apply pair23_eq_of_y_eq S.down_closed (mem_pair23Boundaries.mpr b.2)
          (mem_pair23Boundaries.mpr d.2)
        have bp := b.2.2.2.1; have dp := d.2.2.2.1
        have hv := congrArg (fun x => x.val) (Sum.inl_injective hbd)
        simp at hv; omega
      · simp only [f, dif_pos hby, dif_neg hdy] at hbd; split at hbd <;> contradiction
    · by_cases hdy : d.1.y < g.y
      · simp only [f, dif_neg hby, dif_pos hdy] at hbd; split at hbd <;> contradiction
      · by_cases hbz : b.1.z < g.z
        · by_cases hdz : d.1.z < g.z
          · simp only [f, dif_neg hby, dif_neg hdy, dif_pos hbz, dif_pos hdz] at hbd
            apply Subtype.ext
            apply pair23_eq_of_z_eq S.down_closed (mem_pair23Boundaries.mpr b.2)
              (mem_pair23Boundaries.mpr d.2)
            have bp := b.2.2.2.2; have dp := d.2.2.2.2
            have hv := congrArg (fun x => x.val)
              (Sum.inl_injective (Sum.inr_injective hbd))
            simp at hv; omega
          · simp [f, hby, hdy, hbz, hdz] at hbd
        · by_cases hdz : d.1.z < g.z
          · simp [f, hby, hdy, hbz, hdz] at hbd
          · simp only [f, dif_neg hby, dif_neg hdy, dif_neg hbz, dif_neg hdz] at hbd
            apply pair23ReturnCoord_injective S
            have hb := pair23_terminal_bounds S hg hfull b (by omega) (by omega)
            have hd := pair23_terminal_bounds S hg hfull d (by omega) (by omega)
            have hv := congrArg (fun x => x.val)
              (Sum.inr_injective (Sum.inr_injective hbd))
            simp at hv; omega
  have hcard := Fintype.card_le_of_injective f hf
  simp only [card_pair23Boundary, Fintype.card_sum, Fintype.card_fin] at hcard
  have hx := hfull.1; have hy := hfull.2.1; have hz := hfull.2.2
  omega

theorem pair12_terminal_return_capacity_ordered (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (_hord : PairCountsOrdered S) :
    pair12Count S.D + 2 ≤ g.x + g.y + g.z := by
  have h := pair12_terminal_return_capacity S hg hfull
  have hx := hfull.1; have hy := hfull.2.1; have hz := hfull.2.2
  omega

end NSP3
