import NSP3.BoundaryCard
import NSP3.SymbolicCoordinateTransport

namespace NSP3

/-- Integer ceiling division followed by the exact natural-square-root criterion. -/
theorem quarterSquareCeil_le_sqrt {u m : ℕ} (h : quarterSquareCeil u ≤ m) :
    u ≤ Nat.sqrt (4 * m) := by
  apply Nat.le_sqrt.mpr
  unfold quarterSquareCeil at h
  omega

/-- Unconditional actual boundary-card bound; not a numerical-semigroup presentation theorem. -/
theorem cyclicStaircase_boundary_card_sharp (S : CyclicStaircase) :
    Nat.card {b : Point3 // MinimalComplement S.D b} ≤
      2 + Nat.sqrt (4 * S.m) := by
  classical
  by_cases hfull : ∃ g, MinimalComplement S.D g ∧ FullSupport g
  · obtain ⟨g, hg, hf⟩ := hfull
    have htarget := fullSupport_symbolic_sharp S hg hf
    have hsqrt := quarterSquareCeil_le_sqrt htarget
    rw [boundary_card_of_full S hg hf]
    change pair12Count S.D + pair13Count S.D + pair23Count S.D + 2 ≤ _ at hsqrt
    omega
  · have htarget := noFull_symbolic_sharp S hfull
    have hsqrt := quarterSquareCeil_le_sqrt htarget
    rw [boundary_card_of_noFull S hfull]
    change pair12Count S.D + pair13Count S.D + pair23Count S.D + 1 ≤ _ at hsqrt
    omega

end NSP3
