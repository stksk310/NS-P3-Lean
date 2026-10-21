import NSP3.Main

namespace NSP3

example (m : ℕ) (hm : 4 ≤ m) :
    ∃ S : AddSubmonoid ℕ,
      ((S : Set ℕ)ᶜ).Finite ∧
      semigroupEmbeddingDimension (S : Set ℕ) = 4 ∧
      IsSemigroupMultiplicity (S : Set ℕ) m ∧
      intrinsicRho (S : Set ℕ) = ⌊(2 : ℝ)+2*Real.sqrt (m : ℝ)⌋₊ :=
  all_m_sharp_attainment m hm

example (m : ℕ) (hm : 4 ≤ m) :
    sSup (sharpRhoValues m) = ⌊(2 : ℝ)+2*Real.sqrt (m : ℝ)⌋₊ :=
  all_m_rho_values_sSup m hm

end NSP3
