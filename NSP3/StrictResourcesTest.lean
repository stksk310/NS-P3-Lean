import NSP3.StrictResources

namespace NSP3

example (S : CyclicStaircase) (hof : Pair12OriginFree S) :
    pair12Count S.D + 1 ≤ pure3Intercept S :=
  pair12_originFree_capacity S hof

example (S : CyclicStaircase) (hof : Pair13OriginFree S) :
    pair13Count S.D + 1 ≤ pure2Intercept S :=
  pair13_originFree_capacity S hof

example (S : CyclicStaircase) (hof : Pair23OriginFree S) :
    pair23Count S.D + 1 ≤ pure1Intercept S :=
  pair23_originFree_capacity S hof

example (S : CyclicStaircase) (hof : Pair12OriginFree S) :
    1 ≤ strictAxisExcess3 S := pair12_originFree_strict_resource S hof

example (S : CyclicStaircase) (hs : 2 ≤ pair13Count S.D)
    (hspan : pair23Count S.D * (pair13Count S.D - 1) > pair12Count S.D - 1)
    (hof : Pair13OriginFree S) :
    1 ≤ strictAxisExcess2 S + (pair13ExtraFinset S).card :=
  pair13_originFree_strict_resource S hs hspan hof

example (S : CyclicStaircase) (ht : 2 ≤ pair23Count S.D)
    (hspan : pair13Count S.D * (pair23Count S.D - 1) > pair12Count S.D - 1)
    (hof : Pair23OriginFree S) :
    1 ≤ strictAxisExcess1 S + (pair23ExtraFinset S).card :=
  pair23_originFree_strict_resource S ht hspan hof

end NSP3
