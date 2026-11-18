import P3TorSpike.TorBettiExtrema

/-!
Public entry point for the total Betti results of the accepted21-page manuscript.
The invariant below is defined from Mathlib categorical Tor, not by the claimed
identities. All fields have carrier Type0; actual Tor finiteness is proved.
-/
noncomputable section
namespace NSP3.Betti
open NSP3.TorSpike

abbrev total := torBetti
abbrev dimension := torDimension
abbrev maximumSecond := maximumTorBetti2
abbrev maximumThird := maximumTorBetti3

theorem identities (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    total k m a b c 0 = 1 ∧ total k m a b c 1 = intrinsicRho (generatedSemigroup m a b c) ∧
    total k m a b c 2 = intrinsicRho (generatedSemigroup m a b c) +
      V03.pseudoFrobeniusType m a b c - 1 ∧
    total k m a b c 3 = V03.pseudoFrobeniusType m a b c ∧
    ∀ n, 4 ≤ n → total k m a b c n = 0 :=
  torBetti_identities k m a b c h

theorem finite (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (n : ℕ) :
    Module.Finite k ((ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
      (torModule k m a b c n)) := tor_finite_all k m a b c h n

theorem dimension_eq_total (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (n : ℕ) :
    dimension k m a b c n = (total k m a b c n : Cardinal) :=
  torDimension_eq_torBetti k m a b c h n

theorem upper (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    total k m a b c 1 ≤ V03.T m ∧ total k m a b c 2 ≤ 2 * V03.T m - 2 ∧
      total k m a b c 3 ≤ V03.T m - 1 := torBetti_simultaneous_bounds k m a b c h

theorem noFull_upper (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c)
    (hnf : NoFullSupportBoundary (aperyCyclicStaircase m a b c h.positive h.coprime)) :
    total k m a b c 2 ≤ 2 * V03.T m - 3 ∧ total k m a b c 3 ≤ V03.T m - 2 :=
  torBetti_noFull_bounds k m a b c h hnf

theorem field_independent (k l : Type) [Field k] [Field l] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (n : ℕ) :
    total k m a b c n = total l m a b c n := torBetti_field_independent k l m a b c h n

theorem realized (k : Type) [Field k] (m q : ℕ) (hq : 6 ≤ q) (hb : (q-2)^2 ≤ 4*m) :
    ∃ a b c, ∃ h : MinimalFourGeneratorClass m a b c,
      total k m a b c 0 = 1 ∧ total k m a b c 1 = q ∧
      total k m a b c 2 = 2*q-4 ∧ total k m a b c 3 = q-3 :=
  torBetti_family_realized k m q hq hb

theorem maximumSecond_window (k : Type) [Field k] (m : ℕ) (hm : 4 ≤ m) :
    2 * V03.T m - 4 ≤ maximumSecond k m ∧ maximumSecond k m ≤ 2 * V03.T m - 2 :=
  maximumTorBetti2_window k m hm

theorem maximumThird_window (k : Type) [Field k] (m : ℕ) (hm : 4 ≤ m) :
    V03.T m - 3 ≤ maximumThird k m ∧ maximumThird k m ≤ V03.T m - 1 :=
  maximumTorBetti3_window k m hm

end NSP3.Betti
