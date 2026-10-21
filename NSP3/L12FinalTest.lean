import NSP3.L12Final

example (m : ℕ) (hm : 4 ≤ m) :
    IsGreatest (NSP3.sharpRhoValues m)
      ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ :=
  NSP3.L12_P3_isGreatest m hm

example (m : ℕ) (hm : 4 ≤ m) :
    (NSP3.sharpRhoValues m).Nonempty :=
  ⟨_, (NSP3.L12_P3_isGreatest m hm).1⟩

example (m : ℕ) (hm : 4 ≤ m) :
    BddAbove (NSP3.sharpRhoValues m) :=
  ⟨_, (NSP3.L12_P3_isGreatest m hm).2⟩

example (m : ℕ) (hm : 4 ≤ m) :
    ∃ S : AddSubmonoid ℕ, ((S : Set ℕ)ᶜ).Finite ∧
      NSP3.semigroupEmbeddingDimension (S : Set ℕ) = 4 ∧
      NSP3.IsSemigroupMultiplicity (S : Set ℕ) m ∧
      NSP3.intrinsicRho (S : Set ℕ) =
        ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ :=
  (NSP3.L12_P3_isGreatest m hm).1
