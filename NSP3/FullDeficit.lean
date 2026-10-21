import NSP3.FullAccounting

namespace NSP3

private theorem two_mul_choose_two_full (n : ℕ) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' n.two_dvd_mul_sub_one

private theorem two_mul_choose_two_full_int (n : ℕ) :
    2 * (Nat.choose n 2 : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  cases n with
  | zero => norm_num
  | succ n =>
      have h := two_mul_choose_two_full (n + 1)
      have hz : (2 * Nat.choose (n + 1) 2 : ℤ) =
          ((n + 1) * (n + 1 - 1) : ℕ) := by exact_mod_cast h
      norm_num at hz ⊢
      push_cast at hz
      nlinarith

theorem fullDeficitIdentity (r s t : ℕ) :
    4 * (quarterSquareCeil (r + s + t + 2) : ℤ) +
        ((r : ℤ) - (s : ℤ) - (t : ℤ) + 3) ^ 2 =
      4 * (3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 + Nat.choose t 2 : ℕ) +
        4 * (s : ℤ) * t + 9 + 3 * ((r + s + t + 2) % 2 : ℕ) := by
  have hr2z := two_mul_choose_two_full_int r
  have hs2z := two_mul_choose_two_full_int s
  have ht2z := two_mul_choose_two_full_int t
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (r + s + t + 2)
  · rw [hk, quarterSquareCeil_even]
    have hmod : (2 * k) % 2 = 0 := by omega
    rw [hmod]
    norm_num
    push_cast
    nlinarith
  · rw [hk, quarterSquareCeil_odd]
    have hmod : (2 * k + 1) % 2 = 1 := by omega
    rw [hmod]
    norm_num
    push_cast
    nlinarith

theorem fullTarget_le_fullM_add_product (S : CyclicStaircase) :
    fullTarget S ≤ fullM S + pair13Count S.D * pair23Count S.D + 3 := by
  have hid := fullDeficitIdentity (pair12Count S.D) (pair13Count S.D)
    (pair23Count S.D)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hid
  have hprod : 4 * (pair13Count S.D : ℤ) * pair23Count S.D =
      4 * ((pair13Count S.D : ℤ) * pair23Count S.D) := by ring
  rw [hprod] at hid
  have hsq : (0 : ℤ) ≤ ((pair12Count S.D : ℤ) - pair13Count S.D -
      pair23Count S.D + 3) ^ 2 := sq_nonneg _
  have hmodlt := Nat.mod_lt
    (pair12Count S.D + pair13Count S.D + pair23Count S.D + 2)
    (by norm_num : 0 < 2)
  have hmod : (pair12Count S.D + pair13Count S.D + pair23Count S.D + 2) % 2 ≤ 1 := by
    omega
  have hmodz : (((pair12Count S.D + pair13Count S.D + pair23Count S.D + 2) % 2 : ℕ) : ℤ) ≤ 1 := by
    exact_mod_cast hmod
  have hz : (quarterSquareCeil
      (pair12Count S.D + pair13Count S.D + pair23Count S.D + 2) : ℤ) ≤
      (3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
        Nat.choose (pair13Count S.D) 2 + Nat.choose (pair23Count S.D) 2 +
        pair13Count S.D * pair23Count S.D + 3 : ℕ) := by
    push_cast
    omega
  exact_mod_cast hz

theorem fullDeficit_square_bound (S : CyclicStaircase)
    (hMT : fullM S ≤ fullTarget S) :
    ((pair12Count S.D : ℤ) - pair13Count S.D - pair23Count S.D + 3) ^ 2 ≤
      4 * (pair13Count S.D : ℤ) * pair23Count S.D + 12 := by
  have hid := fullDeficitIdentity (pair12Count S.D) (pair13Count S.D)
    (pair23Count S.D)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hid
  have hmodlt := Nat.mod_lt
    (pair12Count S.D + pair13Count S.D + pair23Count S.D + 2)
    (by norm_num : 0 < 2)
  have hmod : (pair12Count S.D + pair13Count S.D + pair23Count S.D + 2) % 2 ≤ 1 := by
    omega
  have hmodz : (((pair12Count S.D + pair13Count S.D + pair23Count S.D + 2) % 2 : ℕ) : ℤ) ≤ 1 := by
    exact_mod_cast hmod
  have hMTz : (fullM S : ℤ) ≤ (fullTarget S : ℤ) := by exact_mod_cast hMT
  unfold fullTarget fullM at hMTz
  push_cast at hMTz
  omega

end NSP3
