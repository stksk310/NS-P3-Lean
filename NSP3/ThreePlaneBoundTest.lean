import NSP3.ThreePlaneBound

namespace NSP3

example (S : CyclicStaircase) :
    pure1Intercept S + pure2Intercept S + pure3Intercept S - 2
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2 ≤ S.D.card :=
  threePlane_card_lower_D S

example (S : CyclicStaircase) :
    pure1Intercept S + pure2Intercept S + pure3Intercept S - 2
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2 ≤ S.m :=
  threePlane_card_lower S

example : 1 + 1 + 1 - 2 = 1 := by norm_num

end NSP3
