import NSP3.BoundaryFinite
import NSP3.FullBoundaryAPI

namespace NSP3

def allSupportKinds : Finset SupportKind :=
  {.pure1, .pure2, .pure3, .pair12, .pair13, .pair23, .full}

noncomputable def boundarySupport (S : CyclicStaircase) (k : SupportKind) : Finset Point3 := by
  classical
  exact (minimalComplementBoundaries S).filter (HasSupportKind k)

@[simp] theorem mem_boundarySupport (S : CyclicStaircase) (k : SupportKind) (b : Point3) :
    b ∈ boundarySupport S k ↔ MinimalComplement S.D b ∧ HasSupportKind k b := by
  classical
  simp [boundarySupport]

/-- The seven fibers form a genuinely disjoint partition, not just a cover. -/
theorem boundary_support_partition (S : CyclicStaircase) :
    (minimalComplementBoundaries S).card =
      ∑ k ∈ allSupportKinds, (boundarySupport S k).card := by
  classical
  have hcover : allSupportKinds.biUnion (boundarySupport S) =
      minimalComplementBoundaries S := by
    ext b
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨k, _, hb⟩
      exact (mem_minimalComplementBoundaries S b).mpr ((mem_boundarySupport S k b).mp hb).1
    · intro hb
      obtain ⟨k, hk, _⟩ := minimalComplement_supportKind_unique S
        ((mem_minimalComplementBoundaries S b).mp hb)
      exact ⟨k, by cases k <;> simp [allSupportKinds], (mem_boundarySupport S k b).mpr
        ⟨(mem_minimalComplementBoundaries S b).mp hb, hk⟩⟩
  have hdisjoint : (allSupportKinds : Set SupportKind).PairwiseDisjoint
      (boundarySupport S) := by
    intro k _ l _ hkl
    apply Finset.disjoint_left.mpr
    intro b hb hc
    have hb' := (mem_boundarySupport S k b).mp hb
    have hc' := (mem_boundarySupport S l b).mp hc
    obtain ⟨j, _, hj⟩ := minimalComplement_supportKind_unique S hb'.1
    exact hkl ((hj k hb'.2).trans (hj l hc'.2).symm)
  rw [← hcover]
  exact Finset.card_biUnion hdisjoint

private theorem pure1_support_eq (S : CyclicStaircase) :
    boundarySupport S .pure1 = {⟨pure1Intercept S, 0, 0⟩} := by
  classical
  ext b
  rw [mem_boundarySupport, Finset.mem_singleton]
  constructor
  · rintro ⟨hb, hp⟩
    change Pure1 b at hp
    have heq : b = ⟨b.x, 0, 0⟩ := by ext <;> simp [hp.2.1, hp.2.2]
    have ha := pure1_minimalComplement_eq_intercept S (heq ▸ hb) (heq ▸ hp)
    simpa [ha] using heq
  · intro h
    subst b
    exact ⟨pure1Intercept_minimalComplement S, pure1Intercept_pure S⟩

private theorem pure2_support_eq (S : CyclicStaircase) :
    boundarySupport S .pure2 = {⟨0, pure2Intercept S, 0⟩} := by
  classical
  ext b
  rw [mem_boundarySupport, Finset.mem_singleton]
  constructor
  · rintro ⟨hb, hp⟩
    change Pure2 b at hp
    have heq : b = ⟨0, b.y, 0⟩ := by ext <;> simp [hp.1, hp.2.2]
    have ha := pure2_minimalComplement_eq_intercept S (heq ▸ hb) (heq ▸ hp)
    simpa [ha] using heq
  · intro h
    subst b
    exact ⟨pure2Intercept_minimalComplement S, pure2Intercept_pure S⟩

private theorem pure3_support_eq (S : CyclicStaircase) :
    boundarySupport S .pure3 = {⟨0, 0, pure3Intercept S⟩} := by
  classical
  ext b
  rw [mem_boundarySupport, Finset.mem_singleton]
  constructor
  · rintro ⟨hb, hp⟩
    change Pure3 b at hp
    have heq : b = ⟨0, 0, b.z⟩ := by ext <;> simp [hp.1, hp.2.1]
    have ha := pure3_minimalComplement_eq_intercept S (heq ▸ hb) (heq ▸ hp)
    simpa [ha] using heq
  · intro h
    subst b
    exact ⟨pure3Intercept_minimalComplement S, pure3Intercept_pure S⟩

attribute [local instance] Classical.propDecidable

noncomputable def supportBoundaryCard (S : CyclicStaircase) : SupportKind → ℕ
  | .pure1 | .pure2 | .pure3 => 1
  | .pair12 => pair12Count S.D
  | .pair13 => pair13Count S.D
  | .pair23 => pair23Count S.D
  | .full => if ∃ g, MinimalComplement S.D g ∧ FullSupport g then 1 else 0

/-- Every fiber is counted exactly; in particular full support is not an extra assumption. -/
theorem boundary_support_card (S : CyclicStaircase) (k : SupportKind) :
    (boundarySupport S k).card = supportBoundaryCard S k := by
  classical
  cases k with
  | pure1 => simp [pure1_support_eq, supportBoundaryCard]
  | pure2 => simp [pure2_support_eq, supportBoundaryCard]
  | pure3 => simp [pure3_support_eq, supportBoundaryCard]
  | pair12 =>
      have heq : boundarySupport S .pair12 = pair12Boundaries S.D := by
        ext b
        simp [HasSupportKind]
      simp [heq, supportBoundaryCard, pair12Count]
  | pair13 =>
      have heq : boundarySupport S .pair13 = pair13Boundaries S.D := by
        ext b
        simp [HasSupportKind]
      simp [heq, supportBoundaryCard, pair13Count]
  | pair23 =>
      have heq : boundarySupport S .pair23 = pair23Boundaries S.D := by
        ext b
        simp [HasSupportKind]
      simp [heq, supportBoundaryCard, pair23Count]
  | full =>
      dsimp [supportBoundaryCard]
      split_ifs with hfull
      · obtain ⟨g, hg, hf⟩ := hfull
        have heq : boundarySupport S .full = {g} := by
          ext b
          rw [mem_boundarySupport, Finset.mem_singleton]
          constructor
          · rintro ⟨hb, hfb⟩
            exact fullSupportBoundary_unique S hb hfb hg hf
          · intro h
            subst b
            exact ⟨hg, hf⟩
        simp [heq]
      · have heq : boundarySupport S .full = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro b hb
          have hb' := (mem_boundarySupport S .full b).mp hb
          exact hfull ⟨b, hb'.1, hb'.2⟩
        simp [heq]

/-- Exact cardinality of the entire actual minimal-complement boundary. -/
theorem boundary_card_exact (S : CyclicStaircase) :
    Nat.card {b : Point3 // MinimalComplement S.D b} =
      3 + pair12Count S.D + pair13Count S.D + pair23Count S.D +
        (if ∃ g, MinimalComplement S.D g ∧ FullSupport g then 1 else 0) := by
  rw [minimalComplement_card_eq_finset_card, boundary_support_partition]
  simp [allSupportKinds, boundary_support_card, supportBoundaryCard]
  omega

theorem boundary_card_of_full (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    Nat.card {b : Point3 // MinimalComplement S.D b} =
      pair12Count S.D + pair13Count S.D + pair23Count S.D + 4 := by
  rw [boundary_card_exact, ite_eq_left ⟨g, hg, hf⟩]
  omega

theorem boundary_card_of_noFull (S : CyclicStaircase) (hnf : NoFullSupportBoundary S) :
    Nat.card {b : Point3 // MinimalComplement S.D b} =
      pair12Count S.D + pair13Count S.D + pair23Count S.D + 3 := by
  rw [boundary_card_exact, ite_eq_right hnf]
  omega

end NSP3
