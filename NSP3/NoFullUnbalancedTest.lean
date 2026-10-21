import NSP3.NoFullUnbalanced

namespace NSP3

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S) (hlt : pair13Count S.D < pair12Count S.D) :
    noFullTarget S ≤ S.m := noFull_unbalanced_sharp S hnf hord hlt

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S) : noFullTarget S ≤ S.m :=
  noFull_sharp_bound_ordered S hnf hord

end NSP3
