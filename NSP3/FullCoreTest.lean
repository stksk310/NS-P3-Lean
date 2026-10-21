import NSP3.FullCore

namespace NSP3

example (S : CyclicStaircase) (p : Point3) (h : FullCore S p) :
    0 < p.x ∧ 0 < p.y ∧ 0 < p.z := ⟨h.1, h.2.1, h.2.2.1⟩

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S) (p : Point3)
    (hcore : FullCore S p) : p ∈ S.D :=
  noFull_fullCore_mem S hnf hcore

example (S : CyclicStaircase) (p : Point3) :
    p ∈ fullCoreFinset S ↔ FullCore S p :=
  mem_fullCoreFinset S p

example (S : CyclicStaircase) {p : Point3} (hp : p ∈ fullCoreFinset S) :
    FullSupport p :=
  fullSupport_of_mem_fullCoreFinset hp

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S) :
    (fullCoreFinset S).card ≤ S.D.card :=
  fullCore_card_lower S hnf

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S) :
    pure1Intercept S + pure2Intercept S + pure3Intercept S - 2
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + (fullCoreFinset S).card ≤ S.D.card :=
  threePlane_fullCore_card_lower S hnf

example (S : CyclicStaircase)
    (hzero : pair12Count S.D = 0) : fullCoreFinset S = ∅ := by
  ext p
  rw [mem_fullCoreFinset]
  simp only [Finset.notMem_empty, iff_false]
  intro h
  unfold FullCore at h
  rw [hzero] at h
  omega

end NSP3
