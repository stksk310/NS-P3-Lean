import NSP3.StrictAccounting

namespace NSP3

noncomputable example (S : CyclicStaircase) : ℕ := strictAxisExcess1 S
noncomputable example (S : CyclicStaircase) : ℕ := strictAxisExcess2 S
noncomputable example (S : CyclicStaircase) : ℕ := strictAxisExcess3 S
noncomputable example (S : CyclicStaircase) : ℕ := strictResourceExcess S

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S) (hlt : pair13Count S.D < pair12Count S.D) :
    3 * pair12Count S.D
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + (fullCoreFinset S).card + strictResourceExcess S ≤ S.m :=
  strict_resource_accounting S hnf hord hlt

example (S : CyclicStaircase) (hzero : strictResourceExcess S = 0) :
    strictAxisExcess1 S = 0 ∧ strictAxisExcess2 S = 0 ∧
      strictAxisExcess3 S = 0 ∧ (pair12ExtraFinset S).card = 0 ∧
      (pair13ExtraFinset S).card = 0 ∧ (pair23ExtraFinset S).card = 0 :=
  strictResourceExcess_summands_eq_zero S hzero

end NSP3
