import Mathlib

namespace NSP3

theorem positive_triple_product_sum_lower (A B C : ℕ)
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) :
    A+B+C ≤ A*B*C+2 := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hA
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hB
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hC
  ring_nf
  omega

theorem tge4_large_r_gap_identity (r s t : ℤ) :
    4*(4*r+3)+2*r*(r-1)+2*s*(s-1)+2*t*(t-1)-(r+s+t+2)^2 =
      r^2+(10-2*(s+t))*r+(s-t)^2-6*(s+t)+8 := by ring

private theorem choose_two_int (n : ℕ) :
    2*(Nat.choose n 2 : ℤ)+(n : ℤ)=(n : ℤ)^2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    have h : 2*Nat.choose (n+1) 2=(n+1)*((n+1)-1) := by
      rw [Nat.choose_two_right]
      exact Nat.mul_div_cancel' (n+1).two_dvd_mul_sub_one
    norm_num only [Nat.add_sub_cancel] at h
    have hz := h
    zify at hz
    push_cast at hz ⊢
    nlinarith

/-- The positive-box/capacity coarse budget closes every residual strip at r>=18. -/
theorem tge4_large_r_square (r s t m : ℕ) (hr : 18 ≤ r) (hst : s+t ≤ 12)
    (hb : 4*r+3+Nat.choose r 2+Nat.choose s 2+Nat.choose t 2 ≤ m) :
    (r+s+t+2)^2 ≤ 4*m := by
  have cr := choose_two_int r
  have cs := choose_two_int s
  have ct := choose_two_int t
  have hrz : (18 : ℤ) ≤ r := by exact_mod_cast hr
  have hstz : (s : ℤ)+t ≤ 12 := by exact_mod_cast hst
  have hmul : 0 ≤ (12-(s : ℤ)-t)*(r : ℤ) :=
    mul_nonneg (by omega) (by omega)
  have hlarge : 0 ≤ ((r : ℤ)-18)*((r : ℤ)+4) :=
    mul_nonneg (by omega) (by omega)
  have hsq := sq_nonneg ((s : ℤ)-t)
  zify at hb ⊢
  nlinarith only [hb,cr,cs,ct,hmul,hlarge,hsq,hstz]

/-- A stronger symbolic threshold; it reduces the small-width remainder further. -/
theorem tge4_variable_threshold_square (r s t m : ℕ) (hsum : 8 ≤ s+t)
    (hr : 2*(s+t) ≤ r+6)
    (hb : 4*r+3+Nat.choose r 2+Nat.choose s 2+Nat.choose t 2 ≤ m) :
    (r+s+t+2)^2 ≤ 4*m := by
  have cr := choose_two_int r
  have cs := choose_two_int s
  have ct := choose_two_int t
  have hrz : 2*((s : ℤ)+t) ≤ (r : ℤ)+6 := by exact_mod_cast hr
  have hsumz : (8 : ℤ) ≤ (s : ℤ)+t := by exact_mod_cast hsum
  have hmul : 0 ≤ (r : ℤ)*((r : ℤ)+6-2*((s : ℤ)+t)) :=
    mul_nonneg (by omega) (by omega)
  have hsq := sq_nonneg ((s : ℤ)-t)
  zify at hb ⊢
  nlinarith only [hb,cr,cs,ct,hmul,hsq,hrz,hsumz]

end NSP3
