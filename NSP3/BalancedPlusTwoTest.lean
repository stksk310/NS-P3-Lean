import NSP3.BalancedPlusTwo

namespace NSP3

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D)
    (ht : 2 ≤ pair23Count S.D) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + (fullCoreFinset S).card + 2 ≤ S.m :=
  noFull_balanced_plus_two_fullCore S hnf hord heq ht

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D)
    (ht : 2 ≤ pair23Count S.D) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + simplexCard (pair13Count S.D) (pair23Count S.D) + 2 ≤ S.m :=
  noFull_balanced_plus_two S hnf hord heq ht

end NSP3
