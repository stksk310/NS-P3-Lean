import P3Betti

namespace NSP3.TorSpike

private theorem example_class : MinimalFourGeneratorClass 4 7 9 10 := by
  simpa [Sharpness.evenA, Sharpness.evenB, Sharpness.evenC] using
    Sharpness.even_minimalFour 4 1 (by decide) (by decide)

/-- Concrete endpoint check through the actual Tor definition, in every characteristic. -/
theorem fourSevenNineTen_total (k : Type) [Field k] :
    (torBetti k 4 7 9 10 0, torBetti k 4 7 9 10 1,
      torBetti k 4 7 9 10 2, torBetti k 4 7 9 10 3) = (1,6,8,3) := by
  have hρ : intrinsicRho (generatedSemigroup 4 7 9 10) = 6 := by
    simpa [Sharpness.evenA, Sharpness.evenB, Sharpness.evenC] using
      V03.even_family_rho_eq 4 1 (by decide) (by decide)
  have hτ : V03.pseudoFrobeniusType 4 7 9 10 = 3 := by
    rw [V03.pseudoFrobeniusType_eq_finset_card 4 7 9 10
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    simpa [Sharpness.evenA, Sharpness.evenB, Sharpness.evenC] using
      V03.even_numeric_pseudoFrobenius_card 4 1 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨h₀,h₁,h₂,h₃,_⟩ := torBetti_identities k 4 7 9 10 example_class
  simp only [hρ,hτ] at h₁ h₂ h₃
  norm_num at h₂
  simp only [h₀,h₁,h₂,h₃]

example : (torBetti ℚ 4 7 9 10 0, torBetti ℚ 4 7 9 10 1,
    torBetti ℚ 4 7 9 10 2, torBetti ℚ 4 7 9 10 3) = (1,6,8,3) := fourSevenNineTen_total ℚ

example : (torBetti (ZMod 2) 4 7 9 10 0, torBetti (ZMod 2) 4 7 9 10 1,
    torBetti (ZMod 2) 4 7 9 10 2, torBetti (ZMod 2) 4 7 9 10 3) = (1,6,8,3) :=
  fourSevenNineTen_total (ZMod 2)

end NSP3.TorSpike

#print axioms NSP3.TorSpike.Koszul.resolution
#print axioms NSP3.TorSpike.torKoszulFieldIso
#print axioms NSP3.TorSpike.Koszul.torOneConormalFieldIso
#print axioms NSP3.TorSpike.torReducedH3Equiv
#print axioms NSP3.TorSpike.torModule_isZero_from_four
#print axioms NSP3.Betti.finite
#print axioms NSP3.Betti.dimension_eq_total
#print axioms NSP3.Betti.identities
#print axioms NSP3.Betti.field_independent
#print axioms NSP3.Betti.upper
#print axioms NSP3.Betti.noFull_upper
#print axioms NSP3.Betti.realized
#print axioms NSP3.Betti.maximumSecond_window
#print axioms NSP3.Betti.maximumThird_window
#print axioms NSP3.TorSpike.maximumTorBetti2_attained
#print axioms NSP3.TorSpike.maximumTorBetti3_attained
#print axioms NSP3.TorSpike.fourSevenNineTen_total
#check NSP3.Betti.identities
#check NSP3.Betti.finite
#check NSP3.Betti.maximumSecond_window
#check NSP3.Betti.maximumThird_window
