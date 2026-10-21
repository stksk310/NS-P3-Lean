import NSP3.NoFullUnbalanced

namespace NSP3

noncomputable def fullTarget (S : CyclicStaircase) : ℕ :=
  quarterSquareCeil
    (pair12Count S.D + pair13Count S.D + pair23Count S.D + 2)

@[simp] theorem fullTarget_eq (S : CyclicStaircase) :
    fullTarget S = quarterSquareCeil
      (pair12Count S.D + pair13Count S.D + pair23Count S.D + 2) := rfl

theorem fullTarget_eq_square (S : CyclicStaircase) :
    fullTarget S =
      ((pair12Count S.D + pair13Count S.D + pair23Count S.D + 2) ^ 2 + 3) / 4 := by
  simp [fullTarget, quarterSquareCeil, pow_two]

end NSP3
