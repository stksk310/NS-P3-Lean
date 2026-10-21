import NSP3.BalancedResources

namespace NSP3

noncomputable section

example (S : CyclicStaircase) : Prop := Pair12OriginFree S

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S) (heq : pair12Count S.D = pair13Count S.D)
    (ht : 2 ≤ pair23Count S.D) (hof : Pair12OriginFree S) :
    1 ≤ balancedAxisExcess3 S + (pair12ExtraFinset S).card :=
  pair12_originFree_resource S hnf hord heq ht hof

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S) (heq : pair12Count S.D = pair13Count S.D)
    (ht : 2 ≤ pair23Count S.D) (hof : Pair13OriginFree S) :
    1 ≤ balancedAxisExcess2 S + (pair13ExtraFinset S).card :=
  pair13_originFree_resource S hnf hord heq ht hof

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S) (heq : pair12Count S.D = pair13Count S.D)
    (ht : 2 ≤ pair23Count S.D) (hof : Pair23OriginFree S) :
    1 ≤ balancedAxisExcess1 S + (pair23ExtraFinset S).card :=
  pair23_originFree_resource S hnf hord heq ht hof

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S) :
    (Pair12OriginFree S ∧ Pair13OriginFree S) ∨
      (Pair12OriginFree S ∧ Pair23OriginFree S) ∨
      (Pair13OriginFree S ∧ Pair23OriginFree S) :=
  two_pairFamilies_originFree S hnf

end

end NSP3
