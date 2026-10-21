import NSP3.ExactPairPlanes

namespace NSP3


private theorem pair12ExactBoundary_rho (S : CyclicStaircase)
    (hexact : Pair12PlaneExact S) (i : Fin (pair12Count S.D)) :
    S.rho (pair12ExactBoundary S hexact i).1 =
      Point3.mk 0 0 (pair12ExactReturn S hexact i) := by
  apply Point3.ext
  · exact complementFaceReturn₁ S (pair12ExactBoundary S hexact i).2.1
      (pair12ExactBoundary S hexact i).2.2.1
  · exact complementFaceReturn₂ S (pair12ExactBoundary S hexact i).2.1
      (pair12ExactBoundary S hexact i).2.2.2.1
  · rfl

private theorem pair12ExactReturn_adjacent_residue (S : CyclicStaircase)
    (hexact : Pair12PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair12Count S.D) :
    (pair12ExactReturn S hexact ⟨i + 1, hi⟩ : ZMod S.m) * S.p3 + S.p2 =
      (pair12ExactReturn S hexact ⟨i, by omega⟩ : ZMod S.m) * S.p3 + S.p1 := by
  let i0 : Fin (pair12Count S.D) := ⟨i, by omega⟩
  let i1 : Fin (pair12Count S.D) := ⟨i + 1, hi⟩
  have h0 := S.residue_rho (pair12ExactBoundary S hexact i0).1
  have h1 := S.residue_rho (pair12ExactBoundary S hexact i1).1
  rw [pair12ExactBoundary_rho S hexact i0] at h0
  rw [pair12ExactBoundary_rho S hexact i1] at h1
  unfold CyclicStaircase.residue residueOf at h0 h1
  simp only [Nat.cast_zero, zero_mul, zero_add] at h0 h1
  simp [pair12ExactBoundary] at h0 h1
  change
    (pair12ExactReturn S hexact i1 : ZMod S.m) * S.p3 + S.p2 =
      (pair12ExactReturn S hexact i0 : ZMod S.m) * S.p3 + S.p1
  dsimp [i0, i1] at h0 h1 ⊢
  push_cast at h0 h1
  linear_combination h1 - h0

theorem pair12ExactReturn_step_up (S : CyclicStaircase)
    (hexact : Pair12PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair12Count S.D)
    (hlt : pair12ExactReturn S hexact ⟨i, by omega⟩ <
      pair12ExactReturn S hexact ⟨i + 1, hi⟩) :
    pair23Count S.D ≤
      pair12ExactReturn S hexact ⟨i + 1, hi⟩ -
        pair12ExactReturn S hexact ⟨i, by omega⟩ := by
  let c0 := pair12ExactReturn S hexact ⟨i, by omega⟩
  let c1 := pair12ExactReturn S hexact ⟨i + 1, hi⟩
  let d := c1 - c0
  have hdpos : 0 < d := by dsimp [d, c0, c1]; omega
  have hc : c0 + d = c1 := by dsimp [d]; omega
  have hres := pair12ExactReturn_adjacent_residue S hexact hi
  change (c1 : ZMod S.m) * S.p3 + S.p2 = (c0 : ZMod S.m) * S.p3 + S.p1 at hres
  have hgen : S.p1 = S.p2 + (d : ZMod S.m) * S.p3 := by
    rw [← hc] at hres
    simp only [Nat.cast_add] at hres
    linear_combination -hres
  by_contra hnot
  have hdlt : d < pair23Count S.D := Nat.lt_of_not_ge hnot
  have he1 : Point3.e1 ∈ S.D := by
    apply (pure1_axis_mem_iff S 1).mpr
    have h := pair12_intercept1_lower S
    omega
  have h23 : Point3.mk 0 1 d ∈ S.D := by
    apply pair23Triangle_subset S.down_closed (by omega) hdpos
    omega
  have hre : S.residue Point3.e1 = S.residue (Point3.mk 0 1 d) := by
    unfold CyclicStaircase.residue residueOf
    simp only [Point3.e1_x, Point3.e1_y, Point3.e1_z, Nat.cast_one,
      Nat.cast_zero, one_mul, zero_mul, zero_add]
    simpa only [add_zero] using hgen
  have heq := S.standard_eq_of_residue_eq he1 h23 hre
  have hx := congrArg Point3.x heq
  simp [Point3.e1] at hx

theorem pair12ExactReturn_step_down (S : CyclicStaircase)
    (hexact : Pair12PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair12Count S.D)
    (hlt : pair12ExactReturn S hexact ⟨i + 1, hi⟩ <
      pair12ExactReturn S hexact ⟨i, by omega⟩) :
    pair13Count S.D ≤
      pair12ExactReturn S hexact ⟨i, by omega⟩ -
        pair12ExactReturn S hexact ⟨i + 1, hi⟩ := by
  let c0 := pair12ExactReturn S hexact ⟨i, by omega⟩
  let c1 := pair12ExactReturn S hexact ⟨i + 1, hi⟩
  let d := c0 - c1
  have hdpos : 0 < d := by dsimp [d, c0, c1]; omega
  have hc : c1 + d = c0 := by dsimp [d]; omega
  have hres := pair12ExactReturn_adjacent_residue S hexact hi
  change (c1 : ZMod S.m) * S.p3 + S.p2 = (c0 : ZMod S.m) * S.p3 + S.p1 at hres
  have hgen : S.p2 = S.p1 + (d : ZMod S.m) * S.p3 := by
    rw [← hc] at hres
    simp only [Nat.cast_add] at hres
    linear_combination hres
  by_contra hnot
  have hdlt : d < pair13Count S.D := Nat.lt_of_not_ge hnot
  have he2 : Point3.e2 ∈ S.D := by
    apply (pure2_axis_mem_iff S 1).mpr
    have h := pair12_intercept2_lower S
    omega
  have h13 : Point3.mk 1 0 d ∈ S.D := by
    apply pair13Triangle_subset S.down_closed (by omega) hdpos
    omega
  have hre : S.residue Point3.e2 = S.residue (Point3.mk 1 0 d) := by
    unfold CyclicStaircase.residue residueOf
    simp only [Point3.e2_x, Point3.e2_y, Point3.e2_z, Nat.cast_one,
      Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero]
    simpa only [add_zero] using hgen
  have heq := S.standard_eq_of_residue_eq he2 h13 hre
  have hy := congrArg Point3.y heq
  simp [Point3.e2] at hy

private theorem pair13ExactBoundary_rho (S : CyclicStaircase)
    (hexact : Pair13PlaneExact S) (i : Fin (pair13Count S.D)) :
    S.rho (pair13ExactBoundary S hexact i).1 =
      Point3.mk 0 (pair13ExactReturn S hexact i) 0 := by
  apply Point3.ext
  · exact complementFaceReturn₁ S (pair13ExactBoundary S hexact i).2.1
      (pair13ExactBoundary S hexact i).2.2.1
  · rfl
  · exact complementFaceReturn₃ S (pair13ExactBoundary S hexact i).2.1
      (pair13ExactBoundary S hexact i).2.2.2.2

private theorem pair13ExactReturn_adjacent_residue (S : CyclicStaircase)
    (hexact : Pair13PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair13Count S.D) :
    (pair13ExactReturn S hexact ⟨i + 1, hi⟩ : ZMod S.m) * S.p2 + S.p3 =
      (pair13ExactReturn S hexact ⟨i, by omega⟩ : ZMod S.m) * S.p2 + S.p1 := by
  let i0 : Fin (pair13Count S.D) := ⟨i, by omega⟩
  let i1 : Fin (pair13Count S.D) := ⟨i + 1, hi⟩
  have h0 := S.residue_rho (pair13ExactBoundary S hexact i0).1
  have h1 := S.residue_rho (pair13ExactBoundary S hexact i1).1
  rw [pair13ExactBoundary_rho S hexact i0] at h0
  rw [pair13ExactBoundary_rho S hexact i1] at h1
  unfold CyclicStaircase.residue residueOf at h0 h1
  simp only [Nat.cast_zero, zero_mul, zero_add, add_zero] at h0 h1
  simp [pair13ExactBoundary] at h0 h1
  change
    (pair13ExactReturn S hexact i1 : ZMod S.m) * S.p2 + S.p3 =
      (pair13ExactReturn S hexact i0 : ZMod S.m) * S.p2 + S.p1
  dsimp [i0, i1] at h0 h1 ⊢
  push_cast at h0 h1
  linear_combination h1 - h0

theorem pair13ExactReturn_step_up (S : CyclicStaircase)
    (hexact : Pair13PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair13Count S.D)
    (hlt : pair13ExactReturn S hexact ⟨i, by omega⟩ <
      pair13ExactReturn S hexact ⟨i + 1, hi⟩) :
    pair23Count S.D ≤ pair13ExactReturn S hexact ⟨i + 1, hi⟩ -
      pair13ExactReturn S hexact ⟨i, by omega⟩ := by
  let c0 := pair13ExactReturn S hexact ⟨i, by omega⟩
  let c1 := pair13ExactReturn S hexact ⟨i + 1, hi⟩
  let d := c1 - c0
  have hdpos : 0 < d := by dsimp [d, c0, c1]; omega
  have hc : c0 + d = c1 := by dsimp [d]; omega
  have hres := pair13ExactReturn_adjacent_residue S hexact hi
  change (c1 : ZMod S.m) * S.p2 + S.p3 = (c0 : ZMod S.m) * S.p2 + S.p1 at hres
  have hgen : S.p1 = S.p3 + (d : ZMod S.m) * S.p2 := by
    rw [← hc] at hres
    simp only [Nat.cast_add] at hres
    linear_combination -hres
  by_contra hnot
  have hdlt : d < pair23Count S.D := Nat.lt_of_not_ge hnot
  have he1 : Point3.e1 ∈ S.D := by
    apply (pure1_axis_mem_iff S 1).mpr
    have h := pair13_intercept1_lower S
    omega
  have h23 : Point3.mk 0 d 1 ∈ S.D := by
    apply pair23Triangle_subset S.down_closed hdpos (by omega)
    omega
  have hre : S.residue Point3.e1 = S.residue (Point3.mk 0 d 1) := by
    unfold CyclicStaircase.residue residueOf
    simp only [Point3.e1_x, Point3.e1_y, Point3.e1_z, Nat.cast_one,
      Nat.cast_zero, one_mul, zero_mul, zero_add]
    simpa only [add_zero, add_comm] using hgen
  have heq := S.standard_eq_of_residue_eq he1 h23 hre
  have hx := congrArg Point3.x heq
  simp [Point3.e1] at hx

theorem pair13ExactReturn_step_down (S : CyclicStaircase)
    (hexact : Pair13PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair13Count S.D)
    (hlt : pair13ExactReturn S hexact ⟨i + 1, hi⟩ <
      pair13ExactReturn S hexact ⟨i, by omega⟩) :
    pair12Count S.D ≤ pair13ExactReturn S hexact ⟨i, by omega⟩ -
      pair13ExactReturn S hexact ⟨i + 1, hi⟩ := by
  let c0 := pair13ExactReturn S hexact ⟨i, by omega⟩
  let c1 := pair13ExactReturn S hexact ⟨i + 1, hi⟩
  let d := c0 - c1
  have hdpos : 0 < d := by dsimp [d, c0, c1]; omega
  have hc : c1 + d = c0 := by dsimp [d]; omega
  have hres := pair13ExactReturn_adjacent_residue S hexact hi
  change (c1 : ZMod S.m) * S.p2 + S.p3 = (c0 : ZMod S.m) * S.p2 + S.p1 at hres
  have hgen : S.p3 = S.p1 + (d : ZMod S.m) * S.p2 := by
    rw [← hc] at hres
    simp only [Nat.cast_add] at hres
    linear_combination hres
  by_contra hnot
  have hdlt : d < pair12Count S.D := Nat.lt_of_not_ge hnot
  have he3 : Point3.e3 ∈ S.D := by
    apply (pure3_axis_mem_iff S 1).mpr
    have h := pair13_intercept3_lower S
    omega
  have h12 : Point3.mk 1 d 0 ∈ S.D := by
    apply pair12Triangle_subset S.down_closed (by omega) hdpos
    omega
  have hre : S.residue Point3.e3 = S.residue (Point3.mk 1 d 0) := by
    unfold CyclicStaircase.residue residueOf
    simp only [Point3.e3_x, Point3.e3_y, Point3.e3_z, Nat.cast_one,
      Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero]
    exact hgen
  have heq := S.standard_eq_of_residue_eq he3 h12 hre
  have hz := congrArg Point3.z heq
  simp [Point3.e3] at hz

private theorem pair23ExactBoundary_rho (S : CyclicStaircase)
    (hexact : Pair23PlaneExact S) (i : Fin (pair23Count S.D)) :
    S.rho (pair23ExactBoundary S hexact i).1 =
      Point3.mk (pair23ExactReturn S hexact i) 0 0 := by
  apply Point3.ext
  · rfl
  · exact complementFaceReturn₂ S (pair23ExactBoundary S hexact i).2.1
      (pair23ExactBoundary S hexact i).2.2.2.1
  · exact complementFaceReturn₃ S (pair23ExactBoundary S hexact i).2.1
      (pair23ExactBoundary S hexact i).2.2.2.2

private theorem pair23ExactReturn_adjacent_residue (S : CyclicStaircase)
    (hexact : Pair23PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair23Count S.D) :
    (pair23ExactReturn S hexact ⟨i + 1, hi⟩ : ZMod S.m) * S.p1 + S.p3 =
      (pair23ExactReturn S hexact ⟨i, by omega⟩ : ZMod S.m) * S.p1 + S.p2 := by
  let i0 : Fin (pair23Count S.D) := ⟨i, by omega⟩
  let i1 : Fin (pair23Count S.D) := ⟨i + 1, hi⟩
  have h0 := S.residue_rho (pair23ExactBoundary S hexact i0).1
  have h1 := S.residue_rho (pair23ExactBoundary S hexact i1).1
  rw [pair23ExactBoundary_rho S hexact i0] at h0
  rw [pair23ExactBoundary_rho S hexact i1] at h1
  unfold CyclicStaircase.residue residueOf at h0 h1
  simp only [Nat.cast_zero, zero_mul, add_zero] at h0 h1
  simp [pair23ExactBoundary] at h0 h1
  change
    (pair23ExactReturn S hexact i1 : ZMod S.m) * S.p1 + S.p3 =
      (pair23ExactReturn S hexact i0 : ZMod S.m) * S.p1 + S.p2
  dsimp [i0, i1] at h0 h1 ⊢
  push_cast at h0 h1
  linear_combination h1 - h0

theorem pair23ExactReturn_step_up (S : CyclicStaircase)
    (hexact : Pair23PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair23Count S.D)
    (hlt : pair23ExactReturn S hexact ⟨i, by omega⟩ <
      pair23ExactReturn S hexact ⟨i + 1, hi⟩) :
    pair13Count S.D ≤ pair23ExactReturn S hexact ⟨i + 1, hi⟩ -
      pair23ExactReturn S hexact ⟨i, by omega⟩ := by
  let c0 := pair23ExactReturn S hexact ⟨i, by omega⟩
  let c1 := pair23ExactReturn S hexact ⟨i + 1, hi⟩
  let d := c1 - c0
  have hdpos : 0 < d := by dsimp [d, c0, c1]; omega
  have hc : c0 + d = c1 := by dsimp [d]; omega
  have hres := pair23ExactReturn_adjacent_residue S hexact hi
  change (c1 : ZMod S.m) * S.p1 + S.p3 = (c0 : ZMod S.m) * S.p1 + S.p2 at hres
  have hgen : S.p2 = S.p3 + (d : ZMod S.m) * S.p1 := by
    rw [← hc] at hres
    simp only [Nat.cast_add] at hres
    linear_combination -hres
  by_contra hnot
  have hdlt : d < pair13Count S.D := Nat.lt_of_not_ge hnot
  have he2 : Point3.e2 ∈ S.D := by
    apply (pure2_axis_mem_iff S 1).mpr
    have h := pair23_intercept2_lower S
    omega
  have h13 : Point3.mk d 0 1 ∈ S.D := by
    apply pair13Triangle_subset S.down_closed hdpos (by omega)
    omega
  have hre : S.residue Point3.e2 = S.residue (Point3.mk d 0 1) := by
    unfold CyclicStaircase.residue residueOf
    simp only [Point3.e2_x, Point3.e2_y, Point3.e2_z, Nat.cast_one,
      Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero]
    simpa only [add_comm] using hgen
  have heq := S.standard_eq_of_residue_eq he2 h13 hre
  have hy := congrArg Point3.y heq
  simp [Point3.e2] at hy

theorem pair23ExactReturn_step_down (S : CyclicStaircase)
    (hexact : Pair23PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair23Count S.D)
    (hlt : pair23ExactReturn S hexact ⟨i + 1, hi⟩ <
      pair23ExactReturn S hexact ⟨i, by omega⟩) :
    pair12Count S.D ≤ pair23ExactReturn S hexact ⟨i, by omega⟩ -
      pair23ExactReturn S hexact ⟨i + 1, hi⟩ := by
  let c0 := pair23ExactReturn S hexact ⟨i, by omega⟩
  let c1 := pair23ExactReturn S hexact ⟨i + 1, hi⟩
  let d := c0 - c1
  have hdpos : 0 < d := by dsimp [d, c0, c1]; omega
  have hc : c1 + d = c0 := by dsimp [d]; omega
  have hres := pair23ExactReturn_adjacent_residue S hexact hi
  change (c1 : ZMod S.m) * S.p1 + S.p3 = (c0 : ZMod S.m) * S.p1 + S.p2 at hres
  have hgen : S.p3 = S.p2 + (d : ZMod S.m) * S.p1 := by
    rw [← hc] at hres
    simp only [Nat.cast_add] at hres
    linear_combination hres
  by_contra hnot
  have hdlt : d < pair12Count S.D := Nat.lt_of_not_ge hnot
  have he3 : Point3.e3 ∈ S.D := by
    apply (pure3_axis_mem_iff S 1).mpr
    have h := pair23_intercept3_lower S
    omega
  have h12 : Point3.mk d 1 0 ∈ S.D := by
    apply pair12Triangle_subset S.down_closed hdpos (by omega)
    omega
  have hre : S.residue Point3.e3 = S.residue (Point3.mk d 1 0) := by
    unfold CyclicStaircase.residue residueOf
    simp only [Point3.e3_x, Point3.e3_y, Point3.e3_z, Nat.cast_one,
      Nat.cast_zero, one_mul, zero_mul, zero_add, add_zero]
    simpa only [add_comm] using hgen
  have heq := S.standard_eq_of_residue_eq he3 h12 hre
  have hz := congrArg Point3.z heq
  simp [Point3.e3] at hz

end NSP3
