import NSP3.PresentationNormalization

namespace NSP3

/-- Minimum over actual finite generating presentations of the numeric four-input kernel.
The infimum convention outside the existence domain is not used in the bound or attainment proofs. -/
noncomputable def minimumFourInputRelations (m a b c : ℕ) : ℕ :=
  sInf {n : ℕ | ∃ R : Finset (Fact4 × Fact4), IsFactorPresentation m a b c R ∧ R.card = n}

theorem boundary_presentation_card_bound (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    ∃ R : Finset (Fact4 × Fact4), IsFactorPresentation m a b c R ∧
      R.card ≤ Nat.card (PresentationBorder m a b c hm hgcd) :=
  ⟨boundaryRelations m a b c hm hgcd, boundaryRelations_generate m a b c hm hgcd,
    boundaryRelations_card m a b c hm hgcd⟩

theorem minimumFourInputRelations_le (m a b c : ℕ) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R) : minimumFourInputRelations m a b c ≤ R.card :=
  Nat.sInf_le ⟨R,hR,rfl⟩

/-- The minimum is realized by an actual finite presentation, not just a boundary count. -/
theorem minimumFourInputRelations_attained (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    ∃ R : Finset (Fact4 × Fact4), IsFactorPresentation m a b c R ∧
      R.card = minimumFourInputRelations m a b c := by
  have hex : {n : ℕ | ∃ R : Finset (Fact4 × Fact4),
      IsFactorPresentation m a b c R ∧ R.card = n}.Nonempty :=
    ⟨(boundaryRelations m a b c hm hgcd).card,
      boundaryRelations m a b c hm hgcd, boundaryRelations_generate m a b c hm hgcd,rfl⟩
  exact Nat.sInf_mem hex

theorem minimal_presentation_boundary_card_bridge (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    minimumFourInputRelations m a b c ≤
      Nat.card {p : Point3 // MinimalComplement (aperyStandardSet m a b c hm hgcd) p} :=
  (minimumFourInputRelations_le m a b c _ (boundaryRelations_generate m a b c hm hgcd)).trans
    (boundaryRelations_card m a b c hm hgcd)

theorem minimal_presentation_four_input_sharp (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    minimumFourInputRelations m a b c ≤ 2 + Nat.sqrt (4*m) :=
  (minimal_presentation_boundary_card_bridge m a b c hm hgcd).trans
    (apery_boundary_card_sharp m a b c hm hgcd)

theorem minimal_presentation_four_input_real_sharp (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    minimumFourInputRelations m a b c ≤ ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ :=
  (minimal_presentation_boundary_card_bridge m a b c hm hgcd).trans
    (apery_boundary_card_real_sharp m a b c hm hgcd)

end NSP3
