import NSP3.MinimalGeneratorClass

namespace NSP3.Coverage

theorem generated_le (S : AddSubmonoid ℕ) (m a b c : ℕ)
    (hm : m ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    generatedAddSubmonoid m a b c ≤ S := by
  rintro n ⟨k,x,y,z,rfl⟩
  have hk : k*m ∈ S := by simpa [nsmul_eq_mul] using S.nsmul_mem hm k
  have hx : a*x ∈ S := by simpa [nsmul_eq_mul, mul_comm] using S.nsmul_mem ha x
  have hy : b*y ∈ S := by simpa [nsmul_eq_mul, mul_comm] using S.nsmul_mem hb y
  have hz : c*z ∈ S := by simpa [nsmul_eq_mul, mul_comm] using S.nsmul_mem hc z
  exact S.add_mem (S.add_mem (S.add_mem hk hx) hy) hz

theorem common_dvd_generated (m a b c d n : ℕ)
    (hm : d ∣ m) (ha : d ∣ a) (hb : d ∣ b) (hc : d ∣ c)
    (hn : n ∈ generatedSemigroup m a b c) : d ∣ n := by
  obtain ⟨k,x,y,z,rfl⟩ := hn
  exact Nat.dvd_add (Nat.dvd_add (Nat.dvd_add
    (Nat.dvd_mul_left_of_dvd hm k) (Nat.dvd_mul_right_of_dvd ha x))
    (Nat.dvd_mul_right_of_dvd hb y)) (Nat.dvd_mul_right_of_dvd hc z)

theorem gcd_eq_one_of_tail (m a b c C : ℕ)
    (ht : ∀ n, C ≤ n → n ∈ generatedSemigroup m a b c) :
    Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1 := by
  let d := Nat.gcd m (Nat.gcd a (Nat.gcd b c))
  have hm : d ∣ m := Nat.gcd_dvd_left _ _
  have habc : d ∣ Nat.gcd a (Nat.gcd b c) := Nat.gcd_dvd_right _ _
  have ha : d ∣ a := habc.trans (Nat.gcd_dvd_left _ _)
  have hbc : d ∣ Nat.gcd b c := habc.trans (Nat.gcd_dvd_right _ _)
  have hb : d ∣ b := hbc.trans (Nat.gcd_dvd_left _ _)
  have hc : d ∣ c := hbc.trans (Nat.gcd_dvd_right _ _)
  have hC : d ∣ C := common_dvd_generated m a b c d C hm ha hb hc (ht C le_rfl)
  have hnext : d ∣ C+1 := common_dvd_generated m a b c d (C+1) hm ha hb hc (ht (C+1) (by omega))
  exact Nat.dvd_one.mp ((Nat.dvd_add_iff_right hC).mpr hnext)

end NSP3.Coverage
