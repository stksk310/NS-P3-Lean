import NSP3.BalancedAccounting

namespace NSP3

noncomputable def strictAxisExcess1 (S : CyclicStaircase) : ℕ :=
  pure1Intercept S - (pair12Count S.D + 1)

noncomputable def strictAxisExcess2 (S : CyclicStaircase) : ℕ :=
  pure2Intercept S - (pair12Count S.D + 1)

noncomputable def strictAxisExcess3 (S : CyclicStaircase) : ℕ :=
  pure3Intercept S - pair12Count S.D

noncomputable def strictResourceExcess (S : CyclicStaircase) : ℕ :=
  strictAxisExcess1 S + strictAxisExcess2 S + strictAxisExcess3 S
    + (pair12ExtraFinset S).card + (pair13ExtraFinset S).card
    + (pair23ExtraFinset S).card

theorem strict_axis1_baseline (S : CyclicStaircase) :
    pair12Count S.D + 1 ≤ pure1Intercept S := pair12_intercept1_lower S

theorem strict_axis2_baseline (S : CyclicStaircase) :
    pair12Count S.D + 1 ≤ pure2Intercept S := pair12_intercept2_lower S

theorem strict_axis3_baseline (S : CyclicStaircase) :
    pair12Count S.D ≤ pure3Intercept S := pair12_return_capacity S

theorem strict_resource_accounting (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (_hord : PairCountsOrdered S)
    (_hlt : pair13Count S.D < pair12Count S.D) :
    3 * pair12Count S.D
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + (fullCoreFinset S).card + strictResourceExcess S ≤ S.m := by
  have hcard := actualResource_card_lower S hnf
  rw [card_plane12PosFinset, card_plane13PosFinset, card_plane23PosFinset] at hcard
  have h1 := strict_axis1_baseline S
  have h2 := strict_axis2_baseline S
  have h3 := strict_axis3_baseline S
  have hp1 := (pure1Intercept_pure S).1
  have hp2 := (pure2Intercept_pure S).2.1
  have hp3 := (pure3Intercept_pure S).2.2
  have hr : 0 < pair12Count S.D := by omega
  have haxis1 : pure1Intercept S - 1 =
      pair12Count S.D + strictAxisExcess1 S := by
    unfold strictAxisExcess1
    omega
  have haxis2 : pure2Intercept S - 1 =
      pair12Count S.D + strictAxisExcess2 S := by
    unfold strictAxisExcess2
    omega
  have haxis3 : pure3Intercept S - 1 =
      pair12Count S.D - 1 + strictAxisExcess3 S := by
    unfold strictAxisExcess3
    omega
  rw [haxis1, haxis2, haxis3] at hcard
  unfold strictResourceExcess
  omega

theorem strictResourceExcess_summands_eq_zero (S : CyclicStaircase)
    (hzero : strictResourceExcess S = 0) :
    strictAxisExcess1 S = 0 ∧ strictAxisExcess2 S = 0 ∧
      strictAxisExcess3 S = 0 ∧ (pair12ExtraFinset S).card = 0 ∧
      (pair13ExtraFinset S).card = 0 ∧ (pair23ExtraFinset S).card = 0 := by
  unfold strictResourceExcess at hzero
  omega

end NSP3
