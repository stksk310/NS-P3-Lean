import NSP3.Main

example (m : ℕ) (hm : 4 ≤ m) :
    NSP3.P3_R m = NSP3.C3 m ↔ m ≤ 9 := NSP3.P4_e3 m hm

example (m : ℕ) (hm : 10 ≤ m) : NSP3.P3_R m < NSP3.C3 m :=
  NSP3.P4_strict m hm
