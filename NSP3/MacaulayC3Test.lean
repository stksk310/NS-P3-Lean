import NSP3.MacaulayC3

namespace NSP3

example (m : ℕ) (hm : 1 ≤ m) :
    (c3Degree m + 2).choose 3 ≤ m ∧ m < (c3Degree m + 3).choose 3 :=
  c3Degree_interval m hm

example (m r : ℕ) (hm : 1 ≤ m) (hl : (r + 2).choose 3 ≤ m)
    (hu : m < (r + 3).choose 3) : c3Degree m = r :=
  c3Degree_unique m r hm hl hu

example (m : ℕ) (hm : 20 ≤ m) : 4 ≤ c3Degree m := c3Degree_ge_four m hm

example (m : ℕ) (hm : 1 ≤ m) : (c3Degree m + 2).choose 2 ≤ C3 m :=
  C3_ge_binomial m hm

example (m : ℕ) (hm : 1 ≤ m) :
    ∃! r : ℕ, (r + 2).choose 3 ≤ m ∧ m < (r + 3).choose 3 :=
  c3Degree_exists_unique m hm

example (m : ℕ) (hm : 1 ≤ m) :
    c3Remainder m + (c3Degree m + 2).choose 3 = m :=
  c3Remainder_add_base m hm

example (m : ℕ) (hm : 1 ≤ m) :
    c3Remainder m < (c3Degree m + 2).choose 2 :=
  c3Remainder_lt_binomial m hm

example (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (hl : (r + 2).choose (r - 1) ≤ m) (hu : m < (r + 3).choose r) :
    C3 m = (r + 2).choose r +
      macaulayRaise r (m - (r + 2).choose (r - 1)) -
      (m - (r + 2).choose (r - 1)) :=
  C3_original_source_formula m r hm hr hl hu

example (t : ℕ) :
    12 * (((t + 4 + 2).choose 2 - 2)^2) =
      48 * (t + 4 + 3).choose 3 +
        (3*t^4 + 58*t^3 + 375*t^2 + 860*t + 348) :=
  c3_binomial_gap_identity t

example (r m : ℕ) (hr : 4 ≤ r) (hm : m < (r + 3).choose 3) :
    2 + Nat.sqrt (4 * m) < (r + 2).choose 2 :=
  sqrt_bound_lt_binomial r m hr hm

example : c3Degree 4 = 2 := by decide
example : c3Degree 9 = 2 := by decide
example : c3Degree 10 = 3 := by decide
example : c3Degree 19 = 3 := by decide
example : c3Degree 20 = 4 := by decide

end NSP3
