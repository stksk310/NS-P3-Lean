import NSP3.SymbolicSmallwidthRows

namespace NSP3

example (S : CyclicStaircase) (g : Point3) :
    (fullSupportSymbolicH S g).card =
      ∑ y ∈ Finset.Icc 1 (max g.y (pair23Count S.D)),
      ∑ z ∈ Finset.Icc 1 (max g.z (pair23Count S.D)),
        ((fullSupportSymbolicH S g).filter (fun p => p.y=y ∧ p.z=z)).card :=
  symbolic_H_card_eq_sum_rows S g

example (S : CyclicStaircase) : (fullCoreFinset S).card =
    ∑ y ∈ Finset.Icc 1 (pair23Count S.D),
    ∑ z ∈ Finset.Icc 1 (pair23Count S.D),
      if y+z ≤ pair23Count S.D then
        min (pair12Count S.D-y) (pair13Count S.D-z) else 0 :=
  fullCore_card_eq_sum_rows S

end NSP3
