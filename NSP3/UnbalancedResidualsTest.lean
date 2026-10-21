import NSP3.UnbalancedResiduals

namespace NSP3

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S)
    (hsucc : pair12Count S.D = pair13Count S.D + 1)
    (htwo : pair23Count S.D = 2) : noFullTarget S ≤ S.m :=
  noFull_residual_succ_s_2 S hnf hord hsucc htwo

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S)
    (hr : pair12Count S.D = 3) (hs : pair13Count S.D = 2)
    (ht : pair23Count S.D = 2) : noFullTarget S ≤ S.m := by
  apply noFull_residual_succ_s_2 S hnf hord
  · omega
  · exact ht

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S)
    (hr : pair12Count S.D = 4) (hs : pair13Count S.D = 3)
    (ht : pair23Count S.D = 2) : noFullTarget S ≤ S.m := by
  apply noFull_residual_succ_s_2 S hnf hord
  · omega
  · exact ht

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S)
    (hr : pair12Count S.D = 4) (hs : pair13Count S.D = 3)
    (ht : pair23Count S.D = 3) : noFullTarget S ≤ S.m :=
  noFull_residual_433 S hnf hord hr hs ht

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S)
    (hr : pair12Count S.D = 5) (hs : pair13Count S.D = 4)
    (ht : pair23Count S.D = 3) : noFullTarget S ≤ S.m :=
  noFull_residual_543 S hnf hord hr hs ht

end NSP3
