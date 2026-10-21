import NSP3.PairBoundaryCounts

namespace NSP3

noncomputable section

example (S : CyclicStaircase) :
    Fintype.card (Pair12Boundary S) = pair12Count S.D :=
  card_pair12Boundary S

example (S : CyclicStaircase) :
    Fintype.card (Pair13Boundary S) = pair13Count S.D :=
  card_pair13Boundary S

example (S : CyclicStaircase) :
    Fintype.card (Pair23Boundary S) = pair23Count S.D :=
  card_pair23Boundary S

example (S : CyclicStaircase) :
    Pair12Boundary S ≃ {b : Point3 // b ∈ pair12Boundaries S.D} :=
  pair12BoundaryEquiv S

end

end NSP3
