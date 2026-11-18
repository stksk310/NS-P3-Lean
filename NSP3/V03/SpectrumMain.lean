import NSP3.V03.Main
import NSP3.V03.SpectrumLarge
import NSP3.V03.SpectrumRank
import NSP3.V03.SpectrumThree
import NSP3.V03.SpectrumFour
import NSP3.V03.SpectrumFive

namespace NSP3.V03

/-- The full attainable spectrum at every multiplicity at least eight,
on the original intrinsic relation invariant and numerical-semigroup class. -/
theorem spectrum_iff_of_eight_le (m q : ℕ) (hm : 8 ≤ m) :
    q ∈ sharpRhoValues m ↔ 3 ≤ q ∧ q ≤ T m := by
  constructor
  · intro hq
    exact ⟨spectrum_member_ge_three hq,spectrum_member_upper hq⟩
  · rintro ⟨hq,hu⟩
    by_cases h3 : q=3
    · subst q
      exact spectrum_three_exists m hm
    by_cases h4 : q=4
    · subst q
      exact spectrum_four_exists m (by omega)
    by_cases h5 : q=5
    · subst q
      exact spectrum_five_exists m (by omega)
    apply spectrum_large_exists m q (by omega)
    have hs : q-2 ≤ Nat.sqrt (4*m) := by unfold T at hu; omega
    simpa [pow_two] using Nat.le_sqrt.mp hs

theorem spectrum_eq_Icc_of_eight_le (m : ℕ) (hm : 8 ≤ m) :
    sharpRhoValues m=Set.Icc 3 (T m) := by
  ext q
  exact spectrum_iff_of_eight_le m q hm

/-- An equivalent form avoiding real or integer floor notation. -/
theorem spectrum_square_iff_of_eight_le (m q : ℕ) (hm : 8 ≤ m) :
    q ∈ sharpRhoValues m ↔ 3 ≤ q ∧ (q-2)^2 ≤ 4*m := by
  constructor
  · intro hq
    exact ⟨spectrum_member_ge_three hq,spectrum_member_square_bound hq⟩
  · rintro ⟨hq,hs⟩
    apply (spectrum_iff_of_eight_le m q hm).mpr
    refine ⟨hq,?_⟩
    have hl : q-2 ≤ Nat.sqrt (4*m) := Nat.le_sqrt.mpr (by simpa [pow_two] using hs)
    unfold T
    omega

end NSP3.V03
