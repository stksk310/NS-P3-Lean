import NSP3.BalancedAccounting

namespace NSP3

noncomputable section

example (S : CyclicStaircase) : ℕ := balancedAxisExcess1 S
example (S : CyclicStaircase) : ℕ := balancedResourceExcess S

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + (fullCoreFinset S).card
        + balancedResourceExcess S ≤ S.m :=
  balanced_resource_accounting S hnf hord heq

end

end NSP3
