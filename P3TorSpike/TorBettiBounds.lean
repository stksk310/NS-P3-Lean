import P3TorSpike.TorBettiIdentities

noncomputable section
namespace NSP3.TorSpike
open NSP3.V03

theorem torBetti_simultaneous_bounds (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    torBetti k m a b c 1 ≤ T m ∧
    torBetti k m a b c 2 ≤ 2 * T m - 2 ∧
    torBetti k m a b c 3 ≤ T m - 1 := by
  have h₁ : torBetti k m a b c 1 ≤ T m := by
    rw [torBetti_one k m a b c h]
    exact intrinsic_rho_sharp m a b c h
  have h₃ : torBetti k m a b c 3 ≤ T m - 1 := by
    rw [torBetti_three k m a b c h]
    exact pseudoFrobeniusType_upper m a b c h
  have hmid := torBetti_middle k m a b c h
  have hT : 2 ≤ T m := by unfold T; omega
  exact ⟨h₁, by omega, h₃⟩

theorem torBetti_noFull_bounds (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c)
    (hnf : NoFullSupportBoundary (aperyCyclicStaircase m a b c h.positive h.coprime)) :
    torBetti k m a b c 2 ≤ 2 * T m - 3 ∧
    torBetti k m a b c 3 ≤ T m - 2 := by
  have h₁ := (torBetti_simultaneous_bounds k m a b c h).1
  have h₃ : torBetti k m a b c 3 ≤ T m - 2 := by
    rw [torBetti_three k m a b c h]
    exact pseudoFrobeniusType_noFull_upper m a b c h hnf
  have hmid := torBetti_middle k m a b c h
  have hT : 2 ≤ T m := by unfold T; omega
  exact ⟨by omega, h₃⟩

/-- The known numerical-semigroup constructions realize actual total Betti tuples. -/
theorem torBetti_family_realized (k : Type) [Field k] (m q : ℕ) (hq : 6 ≤ q)
    (hbound : (q - 2)^2 ≤ 4*m) :
    ∃ a b c, ∃ h : MinimalFourGeneratorClass m a b c,
      torBetti k m a b c 0 = 1 ∧ torBetti k m a b c 1 = q ∧
      torBetti k m a b c 2 = 2*q - 4 ∧ torBetti k m a b c 3 = q - 3 := by
  obtain ⟨a,b,c,h,hρ,hτ⟩ := presentation_type_window m q hq hbound
  refine ⟨a,b,c,h,torBetti_zero k m a b c h, ?_, ?_, ?_⟩
  · rw [torBetti_one k m a b c h, hρ]
  · have he := torBetti_middle k m a b c h
    rw [torBetti_one k m a b c h, torBetti_three k m a b c h, hρ, hτ] at he
    omega
  · rw [torBetti_three k m a b c h, hτ]

end NSP3.TorSpike
