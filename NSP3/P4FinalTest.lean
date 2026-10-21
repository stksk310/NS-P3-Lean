import NSP3.P4Final

example (m : ℕ) (hm : 4 ≤ m) :
    NSP3.P3_R m = NSP3.C3 m ↔ m ≤ 9 := NSP3.P4_e3 m hm

example : NSP3.P3_R 4 = NSP3.C3 4 := (NSP3.P4_e3 4 (by omega)).2 (by omega)
example : NSP3.P3_R 9 = NSP3.C3 9 := (NSP3.P4_e3 9 (by omega)).2 (by omega)
example : NSP3.P3_R 10 ≠ NSP3.C3 10 := by
  intro h
  have := (NSP3.P4_e3 10 (by omega)).1 h
  omega
example : NSP3.P3_R 20 ≠ NSP3.C3 20 := by
  intro h
  have := (NSP3.P4_e3 20 (by omega)).1 h
  omega

example : NSP3.P3_R 5 = NSP3.C3 5 := (NSP3.P4_e3 5 (by decide)).2 (by decide)
example : NSP3.P3_R 6 = NSP3.C3 6 := (NSP3.P4_e3 6 (by decide)).2 (by decide)
example : NSP3.P3_R 7 = NSP3.C3 7 := (NSP3.P4_e3 7 (by decide)).2 (by decide)
example : NSP3.P3_R 8 = NSP3.C3 8 := (NSP3.P4_e3 8 (by decide)).2 (by decide)
example : NSP3.P3_R 11 < NSP3.C3 11 := NSP3.P4_strict 11 (by decide)
example : NSP3.P3_R 12 < NSP3.C3 12 := NSP3.P4_strict 12 (by decide)
example : NSP3.P3_R 13 < NSP3.C3 13 := NSP3.P4_strict 13 (by decide)
example : NSP3.P3_R 14 < NSP3.C3 14 := NSP3.P4_strict 14 (by decide)
example : NSP3.P3_R 15 < NSP3.C3 15 := NSP3.P4_strict 15 (by decide)
example : NSP3.P3_R 16 < NSP3.C3 16 := NSP3.P4_strict 16 (by decide)
example : NSP3.P3_R 17 < NSP3.C3 17 := NSP3.P4_strict 17 (by decide)
example : NSP3.P3_R 18 < NSP3.C3 18 := NSP3.P4_strict 18 (by decide)
example : NSP3.P3_R 19 < NSP3.C3 19 := NSP3.P4_strict 19 (by decide)

example : [NSP3.C3 4, NSP3.C3 5, NSP3.C3 6, NSP3.C3 7, NSP3.C3 8, NSP3.C3 9] =
    [6, 6, 6, 7, 7, 8] := by decide
example : [NSP3.C3 10, NSP3.C3 11, NSP3.C3 12, NSP3.C3 13, NSP3.C3 14,
    NSP3.C3 15, NSP3.C3 16, NSP3.C3 17, NSP3.C3 18, NSP3.C3 19] =
    [10, 10, 10, 10, 11, 11, 11, 12, 12, 13] := by decide

example (r m : ℕ) (hr : 4 ≤ r) (hm : m < (r+3).choose 3) :
    2 + Nat.sqrt (4*m) < (r+2).choose 2 := NSP3.sqrt_bound_lt_binomial r m hr hm
