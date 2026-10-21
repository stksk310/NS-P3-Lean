import NSP3.PlaneDefects

namespace NSP3

noncomputable def orderedPair12Return (S : CyclicStaircase)
    (i : Fin (pair12Count S.D)) : ℕ :=
  pair12ReturnCoord S (orderedPair12Boundary S i)

noncomputable def orderedPair13Return (S : CyclicStaircase)
    (i : Fin (pair13Count S.D)) : ℕ :=
  pair13ReturnCoord S (orderedPair13Boundary S i)

noncomputable def orderedPair23Return (S : CyclicStaircase)
    (i : Fin (pair23Count S.D)) : ℕ :=
  pair23ReturnCoord S (orderedPair23Boundary S i)

private theorem orderedPair12_rho (S : CyclicStaircase)
    (i : Fin (pair12Count S.D)) :
    S.rho (orderedPair12Boundary S i).1 = Point3.mk 0 0 (orderedPair12Return S i) := by
  apply Point3.ext
  · exact complementFaceReturn₁ S (orderedPair12Boundary S i).2.1
      (orderedPair12Boundary S i).2.2.1
  · exact complementFaceReturn₂ S (orderedPair12Boundary S i).2.1
      (orderedPair12Boundary S i).2.2.2.1
  · rfl

private theorem orderedPair13_rho (S : CyclicStaircase)
    (i : Fin (pair13Count S.D)) :
    S.rho (orderedPair13Boundary S i).1 = Point3.mk 0 (orderedPair13Return S i) 0 := by
  apply Point3.ext
  · exact complementFaceReturn₁ S (orderedPair13Boundary S i).2.1
      (orderedPair13Boundary S i).2.2.1
  · rfl
  · exact complementFaceReturn₃ S (orderedPair13Boundary S i).2.1
      (orderedPair13Boundary S i).2.2.2.2

private theorem orderedPair23_rho (S : CyclicStaircase)
    (i : Fin (pair23Count S.D)) :
    S.rho (orderedPair23Boundary S i).1 = Point3.mk (orderedPair23Return S i) 0 0 := by
  apply Point3.ext
  · rfl
  · exact complementFaceReturn₂ S (orderedPair23Boundary S i).2.1
      (orderedPair23Boundary S i).2.2.2.1
  · exact complementFaceReturn₃ S (orderedPair23Boundary S i).2.1
      (orderedPair23Boundary S i).2.2.2.2

theorem pair12ExactAdjacent_residue (S : CyclicStaircase) {i : ℕ}
    (hi : i + 1 < pair12Count S.D)
    (h0 : (orderedPair12Boundary S ⟨i, by omega⟩).1 =
      Point3.mk (i + 1) (pair12Count S.D - i) 0)
    (h1 : (orderedPair12Boundary S ⟨i + 1, hi⟩).1 =
      Point3.mk (i + 2) (pair12Count S.D - (i + 1)) 0) :
    (orderedPair12Return S ⟨i + 1, hi⟩ : ZMod S.m) * S.p3 + S.p2 =
      (orderedPair12Return S ⟨i, by omega⟩ : ZMod S.m) * S.p3 + S.p1 := by
  let i0 : Fin (pair12Count S.D) := ⟨i, by omega⟩
  let i1 : Fin (pair12Count S.D) := ⟨i + 1, hi⟩
  have r0 := S.residue_rho (orderedPair12Boundary S i0).1
  have r1 := S.residue_rho (orderedPair12Boundary S i1).1
  rw [orderedPair12_rho S i0] at r0
  rw [orderedPair12_rho S i1] at r1
  unfold CyclicStaircase.residue residueOf at r0 r1
  simp only [Nat.cast_zero, zero_mul, zero_add] at r0 r1
  dsimp [i0, i1] at r0 r1 ⊢
  rw [h0] at r0
  rw [h1] at r1
  simp only [Nat.cast_zero, zero_mul, add_zero] at r0 r1
  have hsub : pair12Count S.D - i = pair12Count S.D - (i + 1) + 1 := by omega
  rw [hsub] at r0
  push_cast at r0 r1
  linear_combination r1 - r0

theorem pair13ExactAdjacent_residue (S : CyclicStaircase) {i : ℕ}
    (hi : i + 1 < pair13Count S.D)
    (h0 : (orderedPair13Boundary S ⟨i, by omega⟩).1 =
      Point3.mk (i + 1) 0 (pair13Count S.D - i))
    (h1 : (orderedPair13Boundary S ⟨i + 1, hi⟩).1 =
      Point3.mk (i + 2) 0 (pair13Count S.D - (i + 1))) :
    (orderedPair13Return S ⟨i + 1, hi⟩ : ZMod S.m) * S.p2 + S.p3 =
      (orderedPair13Return S ⟨i, by omega⟩ : ZMod S.m) * S.p2 + S.p1 := by
  let i0 : Fin (pair13Count S.D) := ⟨i, by omega⟩
  let i1 : Fin (pair13Count S.D) := ⟨i + 1, hi⟩
  have r0 := S.residue_rho (orderedPair13Boundary S i0).1
  have r1 := S.residue_rho (orderedPair13Boundary S i1).1
  rw [orderedPair13_rho S i0] at r0
  rw [orderedPair13_rho S i1] at r1
  unfold CyclicStaircase.residue residueOf at r0 r1
  simp only [Nat.cast_zero, zero_mul, zero_add, add_zero] at r0 r1
  dsimp [i0, i1] at r0 r1 ⊢
  rw [h0] at r0
  rw [h1] at r1
  simp only [Nat.cast_zero, zero_mul, add_zero] at r0 r1
  have hsub : pair13Count S.D - i = pair13Count S.D - (i + 1) + 1 := by omega
  rw [hsub] at r0
  push_cast at r0 r1
  linear_combination r1 - r0

theorem pair23ExactAdjacent_residue (S : CyclicStaircase) {i : ℕ}
    (hi : i + 1 < pair23Count S.D)
    (h0 : (orderedPair23Boundary S ⟨i, by omega⟩).1 =
      Point3.mk 0 (i + 1) (pair23Count S.D - i))
    (h1 : (orderedPair23Boundary S ⟨i + 1, hi⟩).1 =
      Point3.mk 0 (i + 2) (pair23Count S.D - (i + 1))) :
    (orderedPair23Return S ⟨i + 1, hi⟩ : ZMod S.m) * S.p1 + S.p3 =
      (orderedPair23Return S ⟨i, by omega⟩ : ZMod S.m) * S.p1 + S.p2 := by
  let i0 : Fin (pair23Count S.D) := ⟨i, by omega⟩
  let i1 : Fin (pair23Count S.D) := ⟨i + 1, hi⟩
  have r0 := S.residue_rho (orderedPair23Boundary S i0).1
  have r1 := S.residue_rho (orderedPair23Boundary S i1).1
  rw [orderedPair23_rho S i0] at r0
  rw [orderedPair23_rho S i1] at r1
  unfold CyclicStaircase.residue residueOf at r0 r1
  simp only [Nat.cast_zero, zero_mul, zero_add, add_zero] at r0 r1
  dsimp [i0, i1] at r0 r1 ⊢
  rw [h0] at r0
  rw [h1] at r1
  simp only [Nat.cast_zero, zero_mul, add_zero] at r0 r1
  have hsub : pair23Count S.D - i = pair23Count S.D - (i + 1) + 1 := by omega
  rw [hsub] at r0
  push_cast at r0 r1
  linear_combination r1 - r0

/-- Local pair-12 upward spacing; only the adjacent residue equation is needed. -/
theorem pair12LocalReturn_step_up (S : CyclicStaircase) {c0 c1 : ℕ}
    (hq : 1 ≤ pair12Count S.D)
    (hres : (c1 : ZMod S.m) * S.p3 + S.p2 = (c0 : ZMod S.m) * S.p3 + S.p1)
    (hlt : c0 < c1) : pair23Count S.D ≤ c1 - c0 := by
  let d := c1 - c0
  have hdpos : 0 < d := by dsimp [d]; omega
  have hc : c0 + d = c1 := by dsimp [d]; omega
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

/-- Local pair-12 downward spacing. -/
theorem pair12LocalReturn_step_down (S : CyclicStaircase) {c0 c1 : ℕ}
    (hq : 1 ≤ pair12Count S.D)
    (hres : (c1 : ZMod S.m) * S.p3 + S.p2 = (c0 : ZMod S.m) * S.p3 + S.p1)
    (hlt : c1 < c0) : pair13Count S.D ≤ c0 - c1 := by
  let d := c0 - c1
  have hdpos : 0 < d := by dsimp [d]; omega
  have hc : c1 + d = c0 := by dsimp [d]; omega
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

/-- Local pair-13 upward spacing. -/
theorem pair13LocalReturn_step_up (S : CyclicStaircase) {c0 c1 : ℕ}
    (hq : 1 ≤ pair13Count S.D)
    (hres : (c1 : ZMod S.m) * S.p2 + S.p3 = (c0 : ZMod S.m) * S.p2 + S.p1)
    (hlt : c0 < c1) : pair23Count S.D ≤ c1 - c0 := by
  let d := c1 - c0
  have hdpos : 0 < d := by dsimp [d]; omega
  have hc : c0 + d = c1 := by dsimp [d]; omega
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

/-- Local pair-13 downward spacing. -/
theorem pair13LocalReturn_step_down (S : CyclicStaircase) {c0 c1 : ℕ}
    (hq : 1 ≤ pair13Count S.D)
    (hres : (c1 : ZMod S.m) * S.p2 + S.p3 = (c0 : ZMod S.m) * S.p2 + S.p1)
    (hlt : c1 < c0) : pair12Count S.D ≤ c0 - c1 := by
  let d := c0 - c1
  have hdpos : 0 < d := by dsimp [d]; omega
  have hc : c1 + d = c0 := by dsimp [d]; omega
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

/-- Local pair-23 upward spacing. -/
theorem pair23LocalReturn_step_up (S : CyclicStaircase) {c0 c1 : ℕ}
    (hq : 1 ≤ pair23Count S.D)
    (hres : (c1 : ZMod S.m) * S.p1 + S.p3 = (c0 : ZMod S.m) * S.p1 + S.p2)
    (hlt : c0 < c1) : pair13Count S.D ≤ c1 - c0 := by
  let d := c1 - c0
  have hdpos : 0 < d := by dsimp [d]; omega
  have hc : c0 + d = c1 := by dsimp [d]; omega
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

/-- Local pair-23 downward spacing. -/
theorem pair23LocalReturn_step_down (S : CyclicStaircase) {c0 c1 : ℕ}
    (hq : 1 ≤ pair23Count S.D)
    (hres : (c1 : ZMod S.m) * S.p1 + S.p3 = (c0 : ZMod S.m) * S.p1 + S.p2)
    (hlt : c1 < c0) : pair12Count S.D ≤ c0 - c1 := by
  let d := c0 - c1
  have hdpos : 0 < d := by dsimp [d]; omega
  have hc : c1 + d = c0 := by dsimp [d]; omega
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

theorem pair12ExactAdjacent_step_up (S : CyclicStaircase) {i : ℕ}
    (hi : i + 1 < pair12Count S.D)
    (h0 : (orderedPair12Boundary S ⟨i, by omega⟩).1 =
      Point3.mk (i + 1) (pair12Count S.D - i) 0)
    (h1 : (orderedPair12Boundary S ⟨i + 1, hi⟩).1 =
      Point3.mk (i + 2) (pair12Count S.D - (i + 1)) 0)
    (hlt : orderedPair12Return S ⟨i, by omega⟩ < orderedPair12Return S ⟨i + 1, hi⟩) :
    pair23Count S.D ≤ orderedPair12Return S ⟨i + 1, hi⟩ -
      orderedPair12Return S ⟨i, by omega⟩ :=
  pair12LocalReturn_step_up S (by omega) (pair12ExactAdjacent_residue S hi h0 h1) hlt

theorem pair12ExactAdjacent_step_down (S : CyclicStaircase) {i : ℕ}
    (hi : i + 1 < pair12Count S.D)
    (h0 : (orderedPair12Boundary S ⟨i, by omega⟩).1 =
      Point3.mk (i + 1) (pair12Count S.D - i) 0)
    (h1 : (orderedPair12Boundary S ⟨i + 1, hi⟩).1 =
      Point3.mk (i + 2) (pair12Count S.D - (i + 1)) 0)
    (hlt : orderedPair12Return S ⟨i + 1, hi⟩ < orderedPair12Return S ⟨i, by omega⟩) :
    pair13Count S.D ≤ orderedPair12Return S ⟨i, by omega⟩ -
      orderedPair12Return S ⟨i + 1, hi⟩ :=
  pair12LocalReturn_step_down S (by omega) (pair12ExactAdjacent_residue S hi h0 h1) hlt

theorem pair13ExactAdjacent_step_up (S : CyclicStaircase) {i : ℕ}
    (hi : i + 1 < pair13Count S.D)
    (h0 : (orderedPair13Boundary S ⟨i, by omega⟩).1 =
      Point3.mk (i + 1) 0 (pair13Count S.D - i))
    (h1 : (orderedPair13Boundary S ⟨i + 1, hi⟩).1 =
      Point3.mk (i + 2) 0 (pair13Count S.D - (i + 1)))
    (hlt : orderedPair13Return S ⟨i, by omega⟩ < orderedPair13Return S ⟨i + 1, hi⟩) :
    pair23Count S.D ≤ orderedPair13Return S ⟨i + 1, hi⟩ -
      orderedPair13Return S ⟨i, by omega⟩ :=
  pair13LocalReturn_step_up S (by omega) (pair13ExactAdjacent_residue S hi h0 h1) hlt

theorem pair13ExactAdjacent_step_down (S : CyclicStaircase) {i : ℕ}
    (hi : i + 1 < pair13Count S.D)
    (h0 : (orderedPair13Boundary S ⟨i, by omega⟩).1 =
      Point3.mk (i + 1) 0 (pair13Count S.D - i))
    (h1 : (orderedPair13Boundary S ⟨i + 1, hi⟩).1 =
      Point3.mk (i + 2) 0 (pair13Count S.D - (i + 1)))
    (hlt : orderedPair13Return S ⟨i + 1, hi⟩ < orderedPair13Return S ⟨i, by omega⟩) :
    pair12Count S.D ≤ orderedPair13Return S ⟨i, by omega⟩ -
      orderedPair13Return S ⟨i + 1, hi⟩ :=
  pair13LocalReturn_step_down S (by omega) (pair13ExactAdjacent_residue S hi h0 h1) hlt

theorem pair23ExactAdjacent_step_up (S : CyclicStaircase) {i : ℕ}
    (hi : i + 1 < pair23Count S.D)
    (h0 : (orderedPair23Boundary S ⟨i, by omega⟩).1 =
      Point3.mk 0 (i + 1) (pair23Count S.D - i))
    (h1 : (orderedPair23Boundary S ⟨i + 1, hi⟩).1 =
      Point3.mk 0 (i + 2) (pair23Count S.D - (i + 1)))
    (hlt : orderedPair23Return S ⟨i, by omega⟩ < orderedPair23Return S ⟨i + 1, hi⟩) :
    pair13Count S.D ≤ orderedPair23Return S ⟨i + 1, hi⟩ -
      orderedPair23Return S ⟨i, by omega⟩ :=
  pair23LocalReturn_step_up S (by omega) (pair23ExactAdjacent_residue S hi h0 h1) hlt

theorem pair23ExactAdjacent_step_down (S : CyclicStaircase) {i : ℕ}
    (hi : i + 1 < pair23Count S.D)
    (h0 : (orderedPair23Boundary S ⟨i, by omega⟩).1 =
      Point3.mk 0 (i + 1) (pair23Count S.D - i))
    (h1 : (orderedPair23Boundary S ⟨i + 1, hi⟩).1 =
      Point3.mk 0 (i + 2) (pair23Count S.D - (i + 1)))
    (hlt : orderedPair23Return S ⟨i + 1, hi⟩ < orderedPair23Return S ⟨i, by omega⟩) :
    pair12Count S.D ≤ orderedPair23Return S ⟨i, by omega⟩ -
      orderedPair23Return S ⟨i + 1, hi⟩ :=
  pair23LocalReturn_step_down S (by omega) (pair23ExactAdjacent_residue S hi h0 h1) hlt

end NSP3
