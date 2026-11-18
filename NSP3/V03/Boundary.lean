import NSP3.V03.CoordinateTransport
import NSP3.AperyBridge
import NSP3.RhoPresentation

namespace NSP3.V03

/-- Actual boundary count, using V03's new ordered capacity inputs. -/
theorem cyclicStaircase_boundary_card_sharp (S : CyclicStaircase) :
    Nat.card {b : Point3 // MinimalComplement S.D b} ≤ 2+Nat.sqrt (4*S.m) := by
  classical
  by_cases hfull : ∃ g, MinimalComplement S.D g ∧ FullSupport g
  · obtain ⟨g,hg,hf⟩ := hfull
    have htarget := fullSupport_symbolic_sharp S hg hf
    have hsqrt := quarterSquareCeil_le_sqrt htarget
    rw [boundary_card_of_full S hg hf]
    change pair12Count S.D+pair13Count S.D+pair23Count S.D+2 ≤ _ at hsqrt
    omega
  · have htarget := noFull_symbolic_sharp S hfull
    have hsqrt := quarterSquareCeil_le_sqrt htarget
    rw [boundary_card_of_noFull S hfull]
    change pair12Count S.D+pair13Count S.D+pair23Count S.D+1 ≤ _ at hsqrt
    omega

theorem apery_boundary_card_sharp (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    Nat.card {p : Point3 // MinimalComplement (aperyStandardSet m a b c hm hgcd) p}
      ≤ 2+Nat.sqrt (4*m) :=
  cyclicStaircase_boundary_card_sharp (aperyCyclicStaircase m a b c hm hgcd)

theorem minimal_presentation_four_input_sharp (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    minimumFourInputRelations m a b c ≤ 2+Nat.sqrt (4*m) :=
  (minimal_presentation_boundary_card_bridge m a b c hm hgcd).trans
    (apery_boundary_card_sharp m a b c hm hgcd)

theorem intrinsic_rho_sharp (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    intrinsicRho (generatedSemigroup m a b c) ≤ 2+Nat.sqrt (4*m) := by
  rw [literature_rho_identification m a b c h]
  exact minimal_presentation_four_input_sharp m a b c h.positive h.coprime

theorem intrinsic_rho_real_sharp (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    intrinsicRho (generatedSemigroup m a b c) ≤ ⌊(2:ℝ)+2*Real.sqrt (m:ℝ)⌋₊ := by
  rw [boundary_real_floor_eq]
  exact intrinsic_rho_sharp m a b c h

end NSP3.V03
