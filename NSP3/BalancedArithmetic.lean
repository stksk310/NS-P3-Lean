import NSP3.BalancedPlusTwo
import NSP3.SimplexPolynomial

namespace NSP3

private theorem two_mul_choose_two (n : ℕ) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' n.two_dvd_mul_sub_one

private theorem six_mul_choose_two (n : ℕ) :
    6 * Nat.choose n 2 = 3 * (n * (n - 1)) := by
  have h := two_mul_choose_two n
  omega

private theorem six_mul_balancedBudget (R t : ℕ) (htr : t ≤ R) :
    6 * (3 * R + 1 + Nat.choose R 2 + Nat.choose R 2 + Nat.choose t 2
        + simplexCard R t + 2) =
      18 * R + 6 + 3 * (R * (R - 1)) + 3 * (R * (R - 1))
        + 3 * (t * (t - 1))
        + t * (t - 1) * (3 * R - 2 * t + 1) + 12 := by
  have hR := six_mul_choose_two R
  have ht := six_mul_choose_two t
  have hs := six_mul_simplexCard R t htr
  calc
    6 * (3 * R + 1 + Nat.choose R 2 + Nat.choose R 2 + Nat.choose t 2
        + simplexCard R t + 2) =
      18 * R + 6 + 6 * Nat.choose R 2 + 6 * Nat.choose R 2
        + 6 * Nat.choose t 2 + 6 * simplexCard R t + 12 := by ring
    _ = 18 * R + 6 + 3 * (R * (R - 1)) + 3 * (R * (R - 1))
        + 3 * (t * (t - 1))
        + t * (t - 1) * (3 * R - 2 * t + 1) + 12 := by
      rw [hR, ht, hs]

theorem balancedTarget_le_m5_simplex_plus_two (R t : ℕ)
    (ht : 2 ≤ t) (htr : t ≤ R) :
    quarterSquareCeil (R + R + t + 1) ≤
      3 * R + 1 + Nat.choose R 2 + Nat.choose R 2 + Nat.choose t 2
        + simplexCard R t + 2 := by
  have hB := six_mul_balancedBudget R t htr
  let d := R - t
  have hR : R = d + t := by
    dsimp [d]
    omega
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' t
  · have hkpos : 1 ≤ k := by omega
    have htarget : quarterSquareCeil (R + R + t + 1) =
        (R + k) * (R + k) + (R + k) + 1 := by
      have harg : R + R + t + 1 = 2 * (R + k) + 1 := by omega
      rw [harg, quarterSquareCeil_odd]
    rw [htarget]
    cases k with
    | zero => omega
    | succ j =>
        rw [hR, hk] at hB ⊢
        have hRm : (d + 2 * (j + 1)) - 1 = d + 2 * j + 1 := by omega
        have htm : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
        have hfac : 3 * (d + 2 * (j + 1)) - 2 * (2 * (j + 1)) + 1 =
            3 * d + 2 * j + 3 := by omega
        rw [hRm, htm, hfac] at hB
        cases j with
        | zero => nlinarith
        | succ l =>
            have hp : 0 ≤ d * (2 * (l + 2) - 1) * (l + 1) := Nat.zero_le _
            have hq : 0 ≤ (l + 1) * l * (4 * (l + 2) + 3) := Nat.zero_le _
            nlinarith
  · have htarget : quarterSquareCeil (R + R + t + 1) =
        (R + k + 1) * (R + k + 1) := by
      have harg : R + R + t + 1 = 2 * (R + k + 1) := by omega
      rw [harg, quarterSquareCeil_even]
    rw [htarget]
    have hkpos : 1 ≤ k := by omega
    cases k with
    | zero => omega
    | succ j =>
        rw [hR, hk] at hB ⊢
        have hRm : (d + (2 * (j + 1) + 1)) - 1 = d + 2 * j + 2 := by omega
        have htm : 2 * (j + 1) + 1 - 1 = 2 * j + 2 := by omega
        have hfac : 3 * (d + (2 * (j + 1) + 1)) - 2 * (2 * (j + 1) + 1) + 1 =
            3 * d + 2 * j + 4 := by omega
        rw [hRm, htm, hfac] at hB
        cases j with
        | zero => nlinarith
        | succ l =>
            have hp : 0 ≤ d * (l + 2) * (2 * (l + 2) - 1) := Nat.zero_le _
            have hq : 0 ≤ (l + 1) * (4 * l * l + 17 * l + 12) := Nat.zero_le _
            nlinarith

theorem balancedTarget_le_m5_t0 (R : ℕ) :
    quarterSquareCeil (R + R + 0 + 1) ≤
      3 * R + 1 + Nat.choose R 2 + Nat.choose R 2 + Nat.choose 0 2 := by
  have htarget : quarterSquareCeil (R + R + 0 + 1) = R * R + R + 1 := by
    have harg : R + R + 0 + 1 = 2 * R + 1 := by omega
    rw [harg, quarterSquareCeil_odd]
  rw [htarget]
  have hc := two_mul_choose_two R
  cases R with
  | zero => simp
  | succ r =>
      simp only [Nat.succ_sub_one] at hc
      norm_num at ⊢
      nlinarith

theorem balancedTarget_le_m5_t1 (R : ℕ) :
    quarterSquareCeil (R + R + 1 + 1) ≤
      3 * R + 1 + Nat.choose R 2 + Nat.choose R 2 + Nat.choose 1 2 := by
  have htarget : quarterSquareCeil (R + R + 1 + 1) = (R + 1) * (R + 1) := by
    have harg : R + R + 1 + 1 = 2 * (R + 1) := by omega
    rw [harg, quarterSquareCeil_even]
  rw [htarget]
  have hc := two_mul_choose_two R
  cases R with
  | zero => simp
  | succ r =>
      simp only [Nat.succ_sub_one] at hc
      norm_num at ⊢
      nlinarith

end NSP3
