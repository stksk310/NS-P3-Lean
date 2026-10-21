import NSP3.NoFullResources

namespace NSP3


example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S)
    (hord : PairCountsOrdered S) (hlt : pair13Count S.D < pair12Count S.D) :
    3 * pair12Count S.D
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + (fullCoreFinset S).card ≤ S.m :=
  m5_fullCore_lower_strict S hnf hord hlt

example (S : CyclicStaircase)
    (hr : pair13Count S.D < pair12Count S.D)
    (ht : pair23Count S.D = 2) :
    pair13Count S.D - 1 ≤ (fullCoreFinset S).card :=
  fullCore_card_lower_t2 S hr ht

example (S : CyclicStaircase)
    (hord : PairCountsOrdered S)
    (hr : pair13Count S.D < pair12Count S.D)
    (ht : pair23Count S.D = 3) :
    3 * pair13Count S.D - 4 ≤ (fullCoreFinset S).card :=
  fullCore_card_lower_t3 S hord hr ht

example (S : CyclicStaircase)
    (hr : 6 ≤ pair12Count S.D)
    (hs : pair13Count S.D = 4) (ht : pair23Count S.D = 4) :
    14 ≤ (fullCoreFinset S).card :=
  fullCore_card_lower_44_large S hr hs ht

example (S : CyclicStaircase)
    (hr : pair12Count S.D = 5)
    (hs : pair13Count S.D = 4) (ht : pair23Count S.D = 4) :
    13 ≤ (fullCoreFinset S).card :=
  fullCore_card_lower_544 S hr hs ht

end NSP3
