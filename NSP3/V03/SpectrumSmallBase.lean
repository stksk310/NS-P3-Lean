import NSP3.V03.SpectrumMain
import NSP3.V03.SpectrumQuadraticLower

namespace NSP3.V03

theorem spectrum_four_iff (m : ℕ) : 4 ∈ sharpRhoValues m ↔ 6 ≤ m :=
  ⟨spectrum_four_multiplicity,spectrum_four_exists m⟩

theorem spectrum_five_iff (m : ℕ) : 5 ∈ sharpRhoValues m ↔ 5 ≤ m :=
  ⟨spectrum_five_multiplicity,spectrum_five_exists m⟩

theorem spectrum_at_four : sharpRhoValues 4=({6} : Set ℕ) := by
  ext q
  constructor
  · intro hq
    have hl := spectrum_member_add_m_ge_ten hq
    have hu := spectrum_member_upper hq
    norm_num at hu
    have he : q=6 := by omega
    exact he
  · intro hq
    have he : q=6 := hq
    subst q
    exact spectrum_large_exists 4 6 (by omega) (by norm_num)

theorem spectrum_at_five : sharpRhoValues 5=({5,6} : Set ℕ) := by
  ext q
  constructor
  · intro hq
    have hl := spectrum_member_add_m_ge_ten hq
    have hu := spectrum_member_upper hq
    norm_num at hu
    change q=5 ∨ q=6
    omega
  · intro hq
    change q=5 ∨ q=6 at hq
    rcases hq with rfl | rfl
    · exact spectrum_five_exists 5 (by omega)
    · exact spectrum_large_exists 5 6 (by omega) (by norm_num)

theorem spectrum_at_six : sharpRhoValues 6=({4,5,6} : Set ℕ) := by
  ext q
  constructor
  · intro hq
    have hl := spectrum_member_add_m_ge_ten hq
    have hu := spectrum_member_upper hq
    norm_num at hu
    change q=4 ∨ q=5 ∨ q=6
    omega
  · intro hq
    change q=4 ∨ q=5 ∨ q=6 at hq
    rcases hq with rfl | rfl | rfl
    · exact spectrum_four_exists 6 (by omega)
    · exact spectrum_five_exists 6 (by omega)
    · exact spectrum_large_exists 6 6 (by omega) (by norm_num)

end NSP3.V03
