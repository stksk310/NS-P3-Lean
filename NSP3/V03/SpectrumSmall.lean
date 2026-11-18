import NSP3.V03.SpectrumSmallBase
import NSP3.V03.SpectrumCubicLower

namespace NSP3.V03

/-- The cubic relation bound transported to the original whole class. -/
theorem spectrum_three_multiplicity {m : ℕ} (hq : 3 ∈ sharpRhoValues m) : 8 ≤ m := by
  rcases hq with ⟨S,hcof,hedim,hmult,hrho⟩
  obtain ⟨a,b,c,h,heq⟩ := numerical_semigroup_class_coverage S m hcof hedim hmult
  have hset : generatedSemigroup m a b c=(S : Set ℕ) :=
    congrArg (fun U : AddSubmonoid ℕ => (U : Set ℕ)) heq
  apply rho_three_multiplicity_ge_eight m a b c h
  simpa only [hset] using hrho

theorem spectrum_three_iff (m : ℕ) : 3 ∈ sharpRhoValues m ↔ 8 ≤ m :=
  ⟨spectrum_three_multiplicity,spectrum_three_exists m⟩

/-- All attainable cardinalities, with no multiplicity restriction and no
change to the pre-existing numerical-semigroup class or invariant. -/
theorem spectrum_all_iff (m q : ℕ) :
    q ∈ sharpRhoValues m ↔
      (q=3 ∧ 8 ≤ m) ∨ (q=4 ∧ 6 ≤ m) ∨ (q=5 ∧ 5 ≤ m) ∨
        (6 ≤ q ∧ q ≤ T m) := by
  constructor
  · intro hq
    have hl := spectrum_member_ge_three hq
    by_cases h3 : q=3
    · subst q
      exact Or.inl ⟨rfl,spectrum_three_multiplicity hq⟩
    by_cases h4 : q=4
    · subst q
      exact Or.inr (Or.inl ⟨rfl,spectrum_four_multiplicity hq⟩)
    by_cases h5 : q=5
    · subst q
      exact Or.inr (Or.inr (Or.inl ⟨rfl,spectrum_five_multiplicity hq⟩))
    exact Or.inr (Or.inr (Or.inr ⟨by omega,spectrum_member_upper hq⟩))
  · rintro (⟨rfl,hm⟩ | ⟨rfl,hm⟩ | ⟨rfl,hm⟩ | ⟨hq,hu⟩)
    · exact spectrum_three_exists m hm
    · exact spectrum_four_exists m hm
    · exact spectrum_five_exists m hm
    · apply spectrum_large_exists m q hq
      have hs : q-2 ≤ Nat.sqrt (4*m) := by unfold T at hu; omega
      simpa [pow_two] using Nat.le_sqrt.mp hs

theorem spectrum_at_seven : sharpRhoValues 7=({4,5,6,7} : Set ℕ) := by
  ext q
  rw [spectrum_all_iff]
  norm_num [T]
  omega

/-- The complete piecewise spectrum in Corollary 4.3 of the frozen V03 paper. -/
theorem complete_spectrum (m : ℕ) (hm : 4 ≤ m) :
    sharpRhoValues m=
      if m=4 then ({6} : Set ℕ)
      else if m=5 then {5,6}
      else if m=6 then {4,5,6}
      else if m=7 then {4,5,6,7}
      else Set.Icc 3 (T m) := by
  split_ifs with h4 h5 h6 h7
  · subst m
    exact spectrum_at_four
  · subst m
    exact spectrum_at_five
  · subst m
    exact spectrum_at_six
  · subst m
    exact spectrum_at_seven
  · exact spectrum_eq_Icc_of_eight_le m (by omega)

end NSP3.V03
