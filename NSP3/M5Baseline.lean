import NSP3.ThreePlaneBound
import NSP3.ModularIntercepts

namespace NSP3

def PairCountsOrdered (S : CyclicStaircase) : Prop :=
  pair23Count S.D ≤ pair13Count S.D ∧
    pair13Count S.D ≤ pair12Count S.D

theorem m4_intercepts_equal (S : CyclicStaircase)
    (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D) :
    3 * pair12Count S.D + 3 ≤
      pure1Intercept S + pure2Intercept S + pure3Intercept S := by
  have _ := hord.1
  have h1 := pair12_intercept1_lower S
  have h2 := pair12_intercept2_lower S
  have h3 := pair13_intercept3_lower S
  omega

theorem m4_intercepts_strict (S : CyclicStaircase)
    (hord : PairCountsOrdered S)
    (hlt : pair13Count S.D < pair12Count S.D) :
    3 * pair12Count S.D + 2 ≤
      pure1Intercept S + pure2Intercept S + pure3Intercept S := by
  have _ := hord.2
  have _ := hlt
  have h1 := pair12_intercept1_lower S
  have h2 := pair12_intercept2_lower S
  have h3 := pair12_return_capacity S
  omega

theorem m4_intercepts_fullSupport (S : CyclicStaircase)
    (hord : PairCountsOrdered S) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    3 * pair12Count S.D + 3 ≤
      pure1Intercept S + pure2Intercept S + pure3Intercept S := by
  have _ := hord.2
  have h1 := pair12_intercept1_lower S
  have h2 := pair12_intercept2_lower S
  have h3 := pair12_return_capacity_fullSupport S hg hfull
  omega

theorem m5_lower_equal (S : CyclicStaircase)
    (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2 ≤ S.m := by
  have hplane := threePlane_card_lower S
  have hm4 := m4_intercepts_equal S hord heq
  have h1 := (pure1Intercept_pure S).1
  have h2 := (pure2Intercept_pure S).2.1
  have h3 := (pure3Intercept_pure S).2.2
  omega

theorem m5_lower_strict (S : CyclicStaircase)
    (hord : PairCountsOrdered S)
    (hlt : pair13Count S.D < pair12Count S.D) :
    3 * pair12Count S.D
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2 ≤ S.m := by
  have hplane := threePlane_card_lower S
  have hm4 := m4_intercepts_strict S hord hlt
  have h1 := (pure1Intercept_pure S).1
  have h2 := (pure2Intercept_pure S).2.1
  have h3 := (pure3Intercept_pure S).2.2
  omega

theorem m5_lower_fullSupport (S : CyclicStaircase)
    (hord : PairCountsOrdered S) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2 ≤ S.m := by
  have hplane := threePlane_card_lower S
  have hm4 := m4_intercepts_fullSupport S hord hg hfull
  have h1 := (pure1Intercept_pure S).1
  have h2 := (pure2Intercept_pure S).2.1
  have h3 := (pure3Intercept_pure S).2.2
  omega

end NSP3
