import NSP3.NoFullBalanced

namespace NSP3

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D) :
    noFullTarget S ≤ S.m :=
  noFull_balanced_sharp S hnf hord heq

end NSP3
