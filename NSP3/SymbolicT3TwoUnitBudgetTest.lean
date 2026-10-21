import NSP3.SymbolicT3TwoUnitBudget
namespace NSP3
example (n : ℕ) (hn : 3 ≤ n) : 2 ≤ ferrersW n 1 1 := two_unit_W_ge_two n hn
example (n : ℕ) (hn : 4 ≤ n) : 4 ≤ ferrersW n 1 1 := two_unit_W_ge_four n hn
example (n h : ℕ) (hn : 3 ≤ n) (hh : n ≤ h) :
    ferrersPlaneDefect n 1 h = h-n+1 := two_unit_defect_long_left n h hn hh
example (n h : ℕ) (hn : 3 ≤ n) (hh : n ≤ h) :
    ferrersPlaneDefect n h 1 = h-n+1 := two_unit_defect_long_right n h hn hh
example (n : ℕ) (hn : 3 ≤ n) :
    ferrersPlaneDefect n 1 1 = ferrersW n 1 1 := two_unit_defect_unit n hn
example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hx : g.x=1) (hz : g.z=1) :
    fullSupportSymbolicBW S g+3 = Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+pair12Count S.D+2*pair13Count S.D+
      min (pair12Count S.D-2) (pair13Count S.D-1)+4*g.y+ferrersW (pair13Count S.D) 1 1 :=
  t3_two_unit_1h1_BW_exact S hg hf ho ht hx hz
example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hx : g.x=1) (hy : g.y=1) :
    fullSupportSymbolicBW S g+3 = Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+2*pair12Count S.D+pair13Count S.D+
      min (pair12Count S.D-2) (pair13Count S.D-1)+4*g.z+ferrersW (pair12Count S.D) 1 1 :=
  t3_two_unit_11h_BW_exact S hg hf ho ht hx hy
-- Hand-derived boundaries, catching off-by-one max/empty-interval errors.
example : ferrersPlaneDefect 3 1 3=1 := by decide
example : ferrersPlaneDefect 3 3 1=1 := by decide
example : ferrersW 3 1 1=2 := by decide
example : ferrersW 4 1 1=4 := by decide
end NSP3
