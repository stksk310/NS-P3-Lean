import NSP3.SharpnessAssembly

namespace NSP3.Sharpness

example (m a b c : ℕ) (P : Point3 → Prop)
    (hu : ∀ p, P p → ∀ t q, aperyWeight a b c p = t*m+aperyWeight a b c q →
      t=0 ∧ q=p) (p : Point3) (hp : P p) (v : CommonCard.FourCoeff)
    (he : CommonCard.degree ![m,a,b,c] (pointFour p) = CommonCard.degree ![m,a,b,c] v) :
    v = pointFour p :=
  pointFour_unique m a b c P hu p hp v he

end NSP3.Sharpness

example (m : ℕ) (hm : 4 ≤ m) :
    ∃ S : AddSubmonoid ℕ,
      ((S : Set ℕ)ᶜ).Finite ∧
      NSP3.semigroupEmbeddingDimension (S : Set ℕ) = 4 ∧
      NSP3.IsSemigroupMultiplicity (S : Set ℕ) m ∧
      NSP3.intrinsicRho (S : Set ℕ) = ⌊(2 : ℝ)+2*Real.sqrt (m : ℝ)⌋₊ :=
  NSP3.all_m_sharp_attainment m hm

example (m : ℕ) (hm : 4 ≤ m) :
    IsGreatest (NSP3.sharpRhoValues m) ⌊(2 : ℝ)+2*Real.sqrt (m : ℝ)⌋₊ :=
  NSP3.all_m_rho_values_isGreatest m hm

example (m : ℕ) (hm : 4 ≤ m) :
    (NSP3.sharpRhoValues m).Nonempty ∧ BddAbove (NSP3.sharpRhoValues m) :=
  ⟨NSP3.all_m_rho_values_nonempty m hm,NSP3.all_m_rho_values_bddAbove m hm⟩

example (m : ℕ) (hm : 4 ≤ m) :
    sSup (NSP3.sharpRhoValues m) = ⌊(2 : ℝ)+2*Real.sqrt (m : ℝ)⌋₊ :=
  NSP3.all_m_rho_values_sSup m hm

example : ∃ S : AddSubmonoid ℕ,
    ((S : Set ℕ)ᶜ).Finite ∧ NSP3.semigroupEmbeddingDimension (S : Set ℕ) = 4 ∧
    NSP3.IsSemigroupMultiplicity (S : Set ℕ) 4 ∧ NSP3.intrinsicRho (S : Set ℕ) = 6 := by
  have h := NSP3.all_m_sharp_attainment 4 (by omega)
  rw [NSP3.boundary_real_floor_eq 4] at h
  norm_num at h
  exact h

example : ∃ S : AddSubmonoid ℕ,
    ((S : Set ℕ)ᶜ).Finite ∧ NSP3.semigroupEmbeddingDimension (S : Set ℕ) = 4 ∧
    NSP3.IsSemigroupMultiplicity (S : Set ℕ) 7 ∧ NSP3.intrinsicRho (S : Set ℕ) = 7 := by
  have h := NSP3.all_m_sharp_attainment 7 (by omega)
  rw [NSP3.boundary_real_floor_eq 7] at h
  norm_num at h
  exact h
