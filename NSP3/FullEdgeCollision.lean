import NSP3.AxisOrder
import NSP3.EdgeCapacity
import NSP3.M5Baseline
import NSP3.PlaneDefects
import NSP3.LocalBlockSpacing

namespace NSP3


/-- Full-branch excess of the first pure intercept over the pair-12 baseline. -/
noncomputable def fullAxisExcess1 (S : CyclicStaircase) : ℕ :=
  pure1Intercept S - (pair12Count S.D + 1)

/-- Full-branch excess of the second pure intercept over the pair-12 baseline. -/
noncomputable def fullAxisExcess2 (S : CyclicStaircase) : ℕ :=
  pure2Intercept S - (pair12Count S.D + 1)

/-- Full-branch excess of the third pure intercept over the pair-12 baseline. -/
noncomputable def fullAxisExcess3 (S : CyclicStaircase) : ℕ :=
  pure3Intercept S - (pair12Count S.D + 1)

noncomputable def pair12BlockReturn (S : CyclicStaircase) (B : Pair12ExactBlock S) :
    Fin B.length → ℕ := fun j =>
  orderedPair12Return S ⟨B.start + j.1,
    lt_of_lt_of_le (Nat.add_lt_add_left j.2 B.start) B.end_le⟩

noncomputable def pair13BlockReturn (S : CyclicStaircase) (B : Pair13ExactBlock S) :
    Fin B.length → ℕ := fun j =>
  orderedPair13Return S ⟨B.start + j.1,
    lt_of_lt_of_le (Nat.add_lt_add_left j.2 B.start) B.end_le⟩

theorem pair12BlockReturn_adjacent_residue (S : CyclicStaircase) (B : Pair12ExactBlock S)
    (j : Fin (B.length - 1)) :
    (pair12BlockReturn S B (edgeRight j) : ZMod S.m) * S.p3 + S.p2 =
      (pair12BlockReturn S B (edgeLeft j) : ZMod S.m) * S.p3 + S.p1 := by
  let n := B.start + j.1
  have hj0 : j.1 < B.length := by omega
  have hj1 : j.1 + 1 < B.length := by omega
  have hend := B.end_le
  have hi : n + 1 < pair12Count S.D := by dsimp [n]; omega
  have h0 := pair12Boundary_eq_diagonal_of_defects_zero S
    ⟨n, by omega⟩ (B.alpha_zero j.1 hj0) (B.gamma_zero j.1 hj0)
  have h1 := pair12Boundary_eq_diagonal_of_defects_zero S
    ⟨n + 1, hi⟩ (B.alpha_zero (j.1 + 1) hj1) (B.gamma_zero (j.1 + 1) hj1)
  have hr := pair12ExactAdjacent_residue S hi h0 h1
  simpa [pair12BlockReturn, edgeLeft, edgeRight, n, Nat.add_assoc] using hr

theorem pair13BlockReturn_adjacent_residue (S : CyclicStaircase) (B : Pair13ExactBlock S)
    (j : Fin (B.length - 1)) :
    (pair13BlockReturn S B (edgeRight j) : ZMod S.m) * S.p2 + S.p3 =
      (pair13BlockReturn S B (edgeLeft j) : ZMod S.m) * S.p2 + S.p1 := by
  let n := B.start + j.1
  have hj0 : j.1 < B.length := by omega
  have hj1 : j.1 + 1 < B.length := by omega
  have hend := B.end_le
  have hi : n + 1 < pair13Count S.D := by dsimp [n]; omega
  have h0 := pair13Boundary_eq_diagonal_of_defects_zero S
    ⟨n, by omega⟩ (B.alpha_zero j.1 hj0) (B.gamma_zero j.1 hj0)
  have h1 := pair13Boundary_eq_diagonal_of_defects_zero S
    ⟨n + 1, hi⟩ (B.alpha_zero (j.1 + 1) hj1) (B.gamma_zero (j.1 + 1) hj1)
  have hr := pair13ExactAdjacent_residue S hi h0 h1
  simpa [pair13BlockReturn, edgeLeft, edgeRight, n, Nat.add_assoc] using hr

private theorem pair12BlockReturn_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) (B : Pair12ExactBlock S)
    (j : Fin B.length) : 1 ≤ pair12BlockReturn S B j := by
  let i : Fin (pair12Count S.D) := ⟨B.start + j.1, by
    have := B.end_le
    omega⟩
  have hne := pair12_return_ne_zero_of_fullSupport S hg hfull
    (orderedPair12Boundary S i).2.1 (orderedPair12Boundary S i).2.2
  by_contra hnot
  have hz : pair12BlockReturn S B j = 0 := Nat.eq_zero_of_not_pos hnot
  apply hne
  apply Point3.ext
  · exact complementFaceReturn₁ S (orderedPair12Boundary S i).2.1
      (orderedPair12Boundary S i).2.2.1
  · exact complementFaceReturn₂ S (orderedPair12Boundary S i).2.1
      (orderedPair12Boundary S i).2.2.2.1
  · simpa [Point3.zero, pair12BlockReturn, orderedPair12Return,
      pair12ReturnCoord, i] using hz

private theorem pair13BlockReturn_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) (B : Pair13ExactBlock S)
    (j : Fin B.length) : 1 ≤ pair13BlockReturn S B j := by
  let i : Fin (pair13Count S.D) := ⟨B.start + j.1, by
    have := B.end_le
    omega⟩
  have hne := pair13_return_ne_zero_of_fullSupport S hg hfull
    (orderedPair13Boundary S i).2.1 (orderedPair13Boundary S i).2.2
  by_contra hnot
  have hz : pair13BlockReturn S B j = 0 := Nat.eq_zero_of_not_pos hnot
  apply hne
  apply Point3.ext
  · exact complementFaceReturn₁ S (orderedPair13Boundary S i).2.1
      (orderedPair13Boundary S i).2.2.1
  · simpa [Point3.zero, pair13BlockReturn, orderedPair13Return,
      pair13ReturnCoord, i] using hz
  · exact complementFaceReturn₃ S (orderedPair13Boundary S i).2.1
      (orderedPair13Boundary S i).2.2.2.2

private theorem pair12BlockReturn_upper (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) (B : Pair12ExactBlock S)
    (j : Fin B.length) :
    pair12BlockReturn S B j ≤ pair12Count S.D + fullAxisExcess3 S := by
  let i : Fin (pair12Count S.D) := ⟨B.start + j.1, by
    have := B.end_le
    omega⟩
  have hrho : S.rho (orderedPair12Boundary S i).1 =
      Point3.mk 0 0 (pair12BlockReturn S B j) := by
    apply Point3.ext
    · exact complementFaceReturn₁ S (orderedPair12Boundary S i).2.1
        (orderedPair12Boundary S i).2.2.1
    · exact complementFaceReturn₂ S (orderedPair12Boundary S i).2.1
        (orderedPair12Boundary S i).2.2.2.1
    · rfl
  have hmem : Point3.mk 0 0 (pair12BlockReturn S B j) ∈ S.D := by
    rw [← hrho]
    exact S.rho_mem _
  have hlt := (pure3_axis_mem_iff S _).mp hmem
  have hcap := pair12_return_capacity_fullSupport S hg hfull
  unfold fullAxisExcess3
  omega

private theorem pair13BlockReturn_upper (S : CyclicStaircase) (B : Pair13ExactBlock S)
    (j : Fin B.length) :
    pair13BlockReturn S B j ≤ pair12Count S.D + fullAxisExcess2 S := by
  let i : Fin (pair13Count S.D) := ⟨B.start + j.1, by
    have := B.end_le
    omega⟩
  have hrho : S.rho (orderedPair13Boundary S i).1 =
      Point3.mk 0 (pair13BlockReturn S B j) 0 := by
    apply Point3.ext
    · exact complementFaceReturn₁ S (orderedPair13Boundary S i).2.1
        (orderedPair13Boundary S i).2.2.1
    · rfl
    · exact complementFaceReturn₃ S (orderedPair13Boundary S i).2.1
        (orderedPair13Boundary S i).2.2.2.2
  have hmem : Point3.mk 0 (pair13BlockReturn S B j) 0 ∈ S.D := by
    rw [← hrho]
    exact S.rho_mem _
  have hlt := (pure2_axis_mem_iff S _).mp hmem
  have hbase := pair12_intercept2_lower S
  unfold fullAxisExcess2
  omega

private theorem pair12BlockReturn_injective (S : CyclicStaircase) (B : Pair12ExactBlock S) :
    Function.Injective (pair12BlockReturn S B) := by
  intro a b hab
  have hb := pair12ReturnCoord_injective S hab
  have hx := congrArg (fun z : Pair12Boundary S => z.1.x) hb
  have hi := (orderedPair12Boundary_x_strictMono S).injective hx
  apply Fin.ext
  have hv := congrArg Fin.val hi
  simp at hv
  omega

private theorem pair13BlockReturn_injective (S : CyclicStaircase) (B : Pair13ExactBlock S) :
    Function.Injective (pair13BlockReturn S B) := by
  intro a b hab
  have hb := pair13ReturnCoord_injective S hab
  have hx := congrArg (fun z : Pair13Boundary S => z.1.x) hb
  have hi := (orderedPair13Boundary_x_strictMono S).injective hx
  apply Fin.ext
  have hv := congrArg Fin.val hi
  simp at hv
  omega

/-- Arithmetic form of the F4.4 application.  The hypotheses deliberately expose
the exact-block length and the negative-spacing estimate, so the theorem can be
reused for either pair plane. -/
theorem positiveJump_bound_of_mixed {L R h d q s e E : ℕ} (c : Fin L → ℕ)
    (hL : 2 ≤ L)
    (hlower : ∀ i, 1 ≤ c i)
    (hupper : ∀ i, c i ≤ R)
    (hinj : Function.Injective c)
    (hh : R + 1 ≤ h)
    (hd : 1 ≤ d)
    (hedge : ∀ i : Fin (L - 1),
      c (edgeRight i) = c (edgeLeft i) + d ∨
      c (edgeLeft i) = c (edgeRight i) + (h - d))
    (hpos : ∃ i : Fin (L - 1), c (edgeRight i) = c (edgeLeft i) + d)
    (hneg : ∃ i : Fin (L - 1), c (edgeLeft i) = c (edgeRight i) + (h - d))
    (hlen : q - e ≤ L)
    (hsPos : 1 ≤ s) (hsQ : s ≤ q)
    (hnegSpace : s ≤ h - d)
    (hR : R = q + E) :
    d - 1 ≤ (q - s) + 2 * E + e := by
  have hcap := cyclicEdgeCapacity c hL hlower hupper hinj hh hd hedge hpos hneg
  rcases le_total e q with heq | hqe <;> omega

/-- Plane-12 naming of the generic positive-jump bound. -/
theorem plane12_positiveJump_bound {L R h d r s e E : ℕ} (c : Fin L → ℕ)
    (hL : 2 ≤ L) (hlower : ∀ i, 1 ≤ c i) (hupper : ∀ i, c i ≤ R)
    (hinj : Function.Injective c) (hh : R + 1 ≤ h) (hd : 1 ≤ d)
    (hedge : ∀ i : Fin (L - 1),
      c (edgeRight i) = c (edgeLeft i) + d ∨
      c (edgeLeft i) = c (edgeRight i) + (h - d))
    (hpos : ∃ i : Fin (L - 1), c (edgeRight i) = c (edgeLeft i) + d)
    (hneg : ∃ i : Fin (L - 1), c (edgeLeft i) = c (edgeRight i) + (h - d))
    (hlen : r - e ≤ L) (hsPos : 1 ≤ s) (hsR : s ≤ r)
    (hnegSpace : s ≤ h - d) (hR : R = r + E) :
    d - 1 ≤ (r - s) + 2 * E + e :=
  positiveJump_bound_of_mixed c hL hlower hupper hinj hh hd hedge hpos hneg
    hlen hsPos hsR hnegSpace hR

/-- Plane-13 naming of the generic positive-jump bound. -/
theorem plane13_positiveJump_bound {L R h d r s e E : ℕ} (c : Fin L → ℕ)
    (hL : 2 ≤ L) (hlower : ∀ i, 1 ≤ c i) (hupper : ∀ i, c i ≤ R)
    (hinj : Function.Injective c) (hh : R + 1 ≤ h) (hd : 1 ≤ d)
    (hedge : ∀ i : Fin (L - 1),
      c (edgeRight i) = c (edgeLeft i) + d ∨
      c (edgeLeft i) = c (edgeRight i) + (h - d))
    (hpos : ∃ i : Fin (L - 1), c (edgeRight i) = c (edgeLeft i) + d)
    (hneg : ∃ i : Fin (L - 1), c (edgeLeft i) = c (edgeRight i) + (h - d))
    (hlen : s - e ≤ L) (hrPos : 1 ≤ r) (hsR : s ≤ r)
    (hnegSpace : r ≤ h - d) (hR : R = r + E) :
    d - 1 ≤ (r - s) + 2 * E + e := by
  have hcap := cyclicEdgeCapacity c hL hlower hupper hinj hh hd hedge hpos hneg
  rcases le_total e s with hes | hse <;> omega

/-- Plane-12 F4.4 (7.2), with the additive order and full-axis range
discharged from the staircase API. -/
theorem plane12_positiveJump_bound_fullSupport (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) {L d : ℕ} (c : Fin L → ℕ)
    (hL : 2 ≤ L) (hsPos : 1 ≤ pair13Count S.D)
    (hlower : ∀ i, 1 ≤ c i)
    (hupper : ∀ i, c i ≤ pair12Count S.D + fullAxisExcess3 S)
    (hinj : Function.Injective c) (hd : 1 ≤ d)
    (hedge : ∀ i : Fin (L - 1),
      c (edgeRight i) = c (edgeLeft i) + d ∨
      c (edgeLeft i) = c (edgeRight i) + (addOrderOf S.p3 - d))
    (hpos : ∃ i : Fin (L - 1), c (edgeRight i) = c (edgeLeft i) + d)
    (hneg : ∃ i : Fin (L - 1),
      c (edgeLeft i) = c (edgeRight i) + (addOrderOf S.p3 - d))
    (hlen : pair12Count S.D - (pair12ExtraFinset S).card ≤ L)
    (hnegSpace : pair13Count S.D ≤ addOrderOf S.p3 - d) :
    d - 1 ≤ (pair12Count S.D - pair13Count S.D) +
      2 * fullAxisExcess3 S + (pair12ExtraFinset S).card := by
  have hi := pair12_return_capacity_fullSupport S hg hfull
  have ho := axis3_addOrder_lower S
  have heq : pure3Intercept S = pair12Count S.D + 1 + fullAxisExcess3 S := by
    unfold fullAxisExcess3
    omega
  have hh : pair12Count S.D + fullAxisExcess3 S + 1 ≤ addOrderOf S.p3 := by
    omega
  exact plane12_positiveJump_bound c hL hlower hupper hinj hh hd hedge hpos hneg
    hlen hsPos hord.2 hnegSpace rfl

/-- Plane-13 F4.4 (7.2), using the second-axis additive order. -/
theorem plane13_positiveJump_bound_fullSupport (S : CyclicStaircase)
    (hord : PairCountsOrdered S) {L d : ℕ} (c : Fin L → ℕ)
    (hL : 2 ≤ L) (hrPos : 1 ≤ pair12Count S.D)
    (hlower : ∀ i, 1 ≤ c i)
    (hupper : ∀ i, c i ≤ pair12Count S.D + fullAxisExcess2 S)
    (hinj : Function.Injective c) (hd : 1 ≤ d)
    (hedge : ∀ i : Fin (L - 1),
      c (edgeRight i) = c (edgeLeft i) + d ∨
      c (edgeLeft i) = c (edgeRight i) + (addOrderOf S.p2 - d))
    (hpos : ∃ i : Fin (L - 1), c (edgeRight i) = c (edgeLeft i) + d)
    (hneg : ∃ i : Fin (L - 1),
      c (edgeLeft i) = c (edgeRight i) + (addOrderOf S.p2 - d))
    (hlen : pair13Count S.D - (pair13ExtraFinset S).card ≤ L)
    (hnegSpace : pair12Count S.D ≤ addOrderOf S.p2 - d) :
    d - 1 ≤ (pair12Count S.D - pair13Count S.D) +
      2 * fullAxisExcess2 S + (pair13ExtraFinset S).card := by
  have hi := pair12_intercept2_lower S
  have ho := axis2_addOrder_lower S
  have heq : pure2Intercept S = pair12Count S.D + 1 + fullAxisExcess2 S := by
    unfold fullAxisExcess2
    omega
  have hh : pair12Count S.D + fullAxisExcess2 S + 1 ≤ addOrderOf S.p2 := by
    omega
  exact plane13_positiveJump_bound c hL hlower hupper hinj hh hd hedge hpos hneg
    hlen hrPos hord.2 hnegSpace rfl

/-- The plane-12 mixed exact block produces the actual positive jump used by F4.4. -/
theorem plane12_positiveJump_of_exactBlock (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (B : Pair12ExactBlock S)
    (hL : 2 ≤ B.length) (hsPos : 1 ≤ pair13Count S.D)
    (hpos : ∃ i : Fin (B.length - 1),
      pair12BlockReturn S B (edgeLeft i) < pair12BlockReturn S B (edgeRight i))
    (hneg : ∃ i : Fin (B.length - 1),
      pair12BlockReturn S B (edgeRight i) < pair12BlockReturn S B (edgeLeft i)) :
    ∃ d, 1 ≤ d ∧ pair23Count S.D ≤ d ∧
      d - 1 ≤ (pair12Count S.D - pair13Count S.D) +
        2 * fullAxisExcess3 S + (pair12ExtraFinset S).card ∧
      S.p1 = S.p2 + (d : ZMod S.m) * S.p3 := by
  let c := pair12BlockReturn S B
  have hlower : ∀ i, 1 ≤ c i := pair12BlockReturn_lower S hg hfull B
  have hupper : ∀ i, c i ≤ pair12Count S.D + fullAxisExcess3 S :=
    pair12BlockReturn_upper S hg hfull B
  have hinj : Function.Injective c := pair12BlockReturn_injective S B
  have hcap := pair12_return_capacity_fullSupport S hg hfull
  have hord3 := axis3_addOrder_lower S
  have hh : pair12Count S.D + fullAxisExcess3 S + 1 ≤ addOrderOf S.p3 := by
    unfold fullAxisExcess3
    omega
  have hres : ∀ i : Fin (B.length - 1),
      (c (edgeRight i) : ZMod S.m) * S.p3 + S.p2 =
        (c (edgeLeft i) : ZMod S.m) * S.p3 + S.p1 :=
    pair12BlockReturn_adjacent_residue S B
  obtain ⟨d, hd, hedge, hup, hdown⟩ :=
    edgeForm_of_commonResidue S.p3 S.p2 S.p1 c hL hlower hupper hinj hh hres hpos hneg
  have hnegSpace : pair13Count S.D ≤ addOrderOf S.p3 - d := by
    obtain ⟨i, hi⟩ := hdown
    have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
      intro heq
      have he := hinj heq
      have hv := congrArg Fin.val he
      simp [edgeLeft, edgeRight] at hv
    have hlt : c (edgeRight i) < c (edgeLeft i) := by omega
    have hs := pair12LocalReturn_step_down S (by
      have := B.end_le
      omega) (hres i) hlt
    omega
  have hbound := plane12_positiveJump_bound_fullSupport S hg hfull hord c hL hsPos
    hlower hupper hinj hd hedge hup hdown B.length_lower hnegSpace
  obtain ⟨i, hi⟩ := hup
  have hr := hres i
  have hposSpace : pair23Count S.D ≤ d := by
    have hlt : c (edgeLeft i) < c (edgeRight i) := by omega
    have hs := pair12LocalReturn_step_up S (by
      have := B.end_le
      omega) hr hlt
    omega
  have hrel : S.p1 = S.p2 + (d : ZMod S.m) * S.p3 := by
    rw [hi] at hr
    push_cast at hr
    linear_combination -hr
  exact ⟨d, hd, hposSpace, hbound, hrel⟩

/-- The plane-13 mixed exact block produces the actual positive jump used by F4.4. -/
theorem plane13_positiveJump_of_exactBlock (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (B : Pair13ExactBlock S)
    (hL : 2 ≤ B.length) (hrPos : 1 ≤ pair12Count S.D)
    (hpos : ∃ i : Fin (B.length - 1),
      pair13BlockReturn S B (edgeLeft i) < pair13BlockReturn S B (edgeRight i))
    (hneg : ∃ i : Fin (B.length - 1),
      pair13BlockReturn S B (edgeRight i) < pair13BlockReturn S B (edgeLeft i)) :
    ∃ d, 1 ≤ d ∧ pair23Count S.D ≤ d ∧
      d - 1 ≤ (pair12Count S.D - pair13Count S.D) +
        2 * fullAxisExcess2 S + (pair13ExtraFinset S).card ∧
      S.p1 = S.p3 + (d : ZMod S.m) * S.p2 := by
  let c := pair13BlockReturn S B
  have hlower : ∀ i, 1 ≤ c i := pair13BlockReturn_lower S hg hfull B
  have hupper : ∀ i, c i ≤ pair12Count S.D + fullAxisExcess2 S :=
    pair13BlockReturn_upper S B
  have hinj : Function.Injective c := pair13BlockReturn_injective S B
  have hbase := pair12_intercept2_lower S
  have hord2 := axis2_addOrder_lower S
  have hh : pair12Count S.D + fullAxisExcess2 S + 1 ≤ addOrderOf S.p2 := by
    unfold fullAxisExcess2
    omega
  have hres : ∀ i : Fin (B.length - 1),
      (c (edgeRight i) : ZMod S.m) * S.p2 + S.p3 =
        (c (edgeLeft i) : ZMod S.m) * S.p2 + S.p1 :=
    pair13BlockReturn_adjacent_residue S B
  obtain ⟨d, hd, hedge, hup, hdown⟩ :=
    edgeForm_of_commonResidue S.p2 S.p3 S.p1 c hL hlower hupper hinj hh hres hpos hneg
  have hnegSpace : pair12Count S.D ≤ addOrderOf S.p2 - d := by
    obtain ⟨i, hi⟩ := hdown
    have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
      intro heq
      have he := hinj heq
      have hv := congrArg Fin.val he
      simp [edgeLeft, edgeRight] at hv
    have hlt : c (edgeRight i) < c (edgeLeft i) := by omega
    have hs := pair13LocalReturn_step_down S (by
      have := B.end_le
      omega) (hres i) hlt
    omega
  have hbound := plane13_positiveJump_bound_fullSupport S hord c hL hrPos
    hlower hupper hinj hd hedge hup hdown B.length_lower hnegSpace
  obtain ⟨i, hi⟩ := hup
  have hr := hres i
  have hposSpace : pair23Count S.D ≤ d := by
    have hlt : c (edgeLeft i) < c (edgeRight i) := by omega
    have hs := pair13LocalReturn_step_up S (by
      have := B.end_le
      omega) hr hlt
    omega
  have hrel : S.p1 = S.p3 + (d : ZMod S.m) * S.p2 := by
    rw [hi] at hr
    push_cast at hr
    linear_combination -hr
  exact ⟨d, hd, hposSpace, hbound, hrel⟩

/-- Equal residues of two positive standard points on different axes are impossible. -/
theorem twoAxis_standard_collision (S : CyclicStaircase) {u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (huStd : u < pure2Intercept S) (hvStd : v < pure3Intercept S)
    (hres : (u : ZMod S.m) * S.p2 = (v : ZMod S.m) * S.p3) : False := by
  have h2 : Point3.mk 0 u 0 ∈ S.D := (pure2_axis_mem_iff S u).mpr huStd
  have h3 : Point3.mk 0 0 v ∈ S.D := (pure3_axis_mem_iff S v).mpr hvStd
  have hr : S.residue (Point3.mk 0 u 0) = S.residue (Point3.mk 0 0 v) := by
    simpa [CyclicStaircase.residue, residueOf] using hres
  have heq := S.standard_eq_of_residue_eq h2 h3 hr
  have hy := congrArg Point3.y heq
  change u = 0 at hy
  omega

/-- The F4.4 two-axis collision endpoint.  The numerical bounds put both
coefficients on the standard axes; the residue relation then violates standard
residue injectivity. -/
theorem fullSupport_twoAxisCollision (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    {d2 d3 : ℕ}
    (hd2 : 2 ≤ d2) (hd3 : 2 ≤ d3)
    (hb2 : d2 - 1 ≤ pair12Count S.D)
    (hb3 : d3 - 1 ≤ pair12Count S.D)
    (hres : (d2 - 1 : ℕ) • S.p2 = (d3 - 1 : ℕ) • S.p3) : False := by
  have hi2 := pair12_intercept2_lower S
  have hi3 := pair12_return_capacity_fullSupport S hg hfull
  apply twoAxis_standard_collision S (u := d2 - 1) (v := d3 - 1)
  · omega
  · omega
  · omega
  · omega
  · simpa [nsmul_eq_mul] using hres

/-- The global defect/excess budget turns the two F4.4 jump bounds into the
standard-axis collision required by the endpoint theorem. -/
theorem fullSupport_twoAxisCollision_of_budget (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    {d2 d3 K : ℕ} (ht : 2 ≤ pair23Count S.D)
    (hd2Lower : pair23Count S.D ≤ d2) (hd3Lower : pair23Count S.D ≤ d3)
    (hb2 : d2 - 1 ≤ (pair12Count S.D - pair13Count S.D) +
      2 * fullAxisExcess2 S + (pair13ExtraFinset S).card)
    (hb3 : d3 - 1 ≤ (pair12Count S.D - pair13Count S.D) +
      2 * fullAxisExcess3 S + (pair12ExtraFinset S).card)
    (hK : fullAxisExcess2 S + fullAxisExcess3 S +
      (pair12ExtraFinset S).card + (pair13ExtraFinset S).card ≤ K)
    (hbudget : (pair12Count S.D - pair13Count S.D) + 2 * K ≤ pair12Count S.D)
    (hrel2 : S.p1 = S.p3 + (d2 : ZMod S.m) * S.p2)
    (hrel3 : S.p1 = S.p2 + (d3 : ZMod S.m) * S.p3) : False := by
  have hd2 : 2 ≤ d2 := by omega
  have hd3 : 2 ≤ d3 := by omega
  have hcoef2 : d2 - 1 ≤ pair12Count S.D := by omega
  have hcoef3 : d3 - 1 ≤ pair12Count S.D := by omega
  have hres : (d2 - 1 : ℕ) • S.p2 = (d3 - 1 : ℕ) • S.p3 := by
    have heq : (d2 : ZMod S.m) * S.p2 - S.p2 =
        (d3 : ZMod S.m) * S.p3 - S.p3 := by
      have h := hrel2.symm.trans hrel3
      linear_combination h
    simpa [nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ d2),
      Nat.cast_sub (by omega : 1 ≤ d3), sub_mul] using heq
  exact fullSupport_twoAxisCollision S hg hfull hd2 hd3 hcoef2 hcoef3 hres

/-- Contract-shaped M9 theorem: two mixed exact blocks, the `t ≥ 2`
hypothesis, and the global budget already contradict full support. -/
theorem fullSupport_mixedExactBlocks_impossible (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (B12 : Pair12ExactBlock S) (B13 : Pair13ExactBlock S)
    (hL12 : 2 ≤ B12.length) (hL13 : 2 ≤ B13.length)
    (ht : 2 ≤ pair23Count S.D) (hsPos : 1 ≤ pair13Count S.D)
    (h12pos : ∃ i : Fin (B12.length - 1),
      pair12BlockReturn S B12 (edgeLeft i) < pair12BlockReturn S B12 (edgeRight i))
    (h12neg : ∃ i : Fin (B12.length - 1),
      pair12BlockReturn S B12 (edgeRight i) < pair12BlockReturn S B12 (edgeLeft i))
    (h13pos : ∃ i : Fin (B13.length - 1),
      pair13BlockReturn S B13 (edgeLeft i) < pair13BlockReturn S B13 (edgeRight i))
    (h13neg : ∃ i : Fin (B13.length - 1),
      pair13BlockReturn S B13 (edgeRight i) < pair13BlockReturn S B13 (edgeLeft i))
    {K : ℕ}
    (hK : fullAxisExcess2 S + fullAxisExcess3 S +
      (pair12ExtraFinset S).card + (pair13ExtraFinset S).card ≤ K)
    (hbudget : (pair12Count S.D - pair13Count S.D) + 2 * K ≤ pair12Count S.D) :
    False := by
  obtain ⟨d3, _hd3, hd3Lower, hb3, hrel3⟩ :=
    plane12_positiveJump_of_exactBlock S hg hfull hord B12 hL12 hsPos h12pos h12neg
  obtain ⟨d2, _hd2, hd2Lower, hb2, hrel2⟩ :=
    plane13_positiveJump_of_exactBlock S hg hfull hord B13 hL13 (by omega) h13pos h13neg
  exact fullSupport_twoAxisCollision_of_budget S hg hfull ht hd2Lower hd3Lower
    hb2 hb3 hK hbudget hrel2 hrel3

end NSP3
