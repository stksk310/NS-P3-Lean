import NSP3.M5Baseline

namespace NSP3

example (S : CyclicStaircase) : Prop := PairCountsOrdered S

example (S : CyclicStaircase) (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D) :
    3 * pair12Count S.D + 3 ≤
      pure1Intercept S + pure2Intercept S + pure3Intercept S :=
  m4_intercepts_equal S hord heq

example (S : CyclicStaircase) (hord : PairCountsOrdered S)
    (hlt : pair13Count S.D < pair12Count S.D) :
    3 * pair12Count S.D + 2 ≤
      pure1Intercept S + pure2Intercept S + pure3Intercept S :=
  m4_intercepts_strict S hord hlt

example (S : CyclicStaircase) (hord : PairCountsOrdered S) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    3 * pair12Count S.D + 3 ≤
      pure1Intercept S + pure2Intercept S + pure3Intercept S :=
  m4_intercepts_fullSupport S hord hg hfull

example (S : CyclicStaircase) (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2 ≤ S.m :=
  m5_lower_equal S hord heq

example (S : CyclicStaircase) (hord : PairCountsOrdered S)
    (hlt : pair13Count S.D < pair12Count S.D) :
    3 * pair12Count S.D
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2 ≤ S.m :=
  m5_lower_strict S hord hlt

example (S : CyclicStaircase) (hord : PairCountsOrdered S) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2 ≤ S.m :=
  m5_lower_fullSupport S hord hg hfull

-- Small boundary arithmetic for the equal branch: q12 = q13 = 1, q23 = 0.
example : 3 * 1 + 1 + Nat.choose 1 2 + Nat.choose 1 2 + Nat.choose 0 2 = 4 := by
  norm_num [Nat.choose]

-- Small boundary arithmetic for the strict branch: q12 = 1, q13 = q23 = 0.
example : 3 * 1 + Nat.choose 1 2 + Nat.choose 0 2 + Nat.choose 0 2 = 3 := by
  norm_num [Nat.choose]

end NSP3
