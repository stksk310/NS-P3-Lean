import NSP3.V03

example (m : ℕ) (hm : 4 ≤ m) : NSP3.P3_R m=NSP3.V03.T m :=
  NSP3.V03.P3_MAIN m hm

example (m : ℕ) (hm : 4 ≤ m) : NSP3.P3_R m=NSP3.C3 m ↔ m ≤ 9 :=
  NSP3.V03.P4_e3 m hm

example (m : ℕ) (hm : 4 ≤ m) :
    NSP3.V03.T m-3 ≤ NSP3.V03.maximumType m ∧
      NSP3.V03.maximumType m ≤ NSP3.V03.T m-1 :=
  NSP3.V03.maximumType_window m hm
