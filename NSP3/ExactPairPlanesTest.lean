import NSP3.ExactPairPlanes

namespace NSP3

noncomputable section

example (S : CyclicStaircase) (h : Pair12PlaneExact S)
    (i : Fin (pair12Count S.D)) : Pair12Boundary S :=
  pair12ExactBoundary S h i

example (S : CyclicStaircase) (h : Pair13PlaneExact S)
    (i : Fin (pair13Count S.D)) : Pair13Boundary S :=
  pair13ExactBoundary S h i

example (S : CyclicStaircase) (h : Pair23PlaneExact S)
    (i : Fin (pair23Count S.D)) : Pair23Boundary S :=
  pair23ExactBoundary S h i

example (S : CyclicStaircase) (h : Pair12PlaneExact S)
    {i : ℕ} (hi : i + 1 < pair12Count S.D) :
    pair12ExactReturn S h ⟨i, by omega⟩ ≠
      pair12ExactReturn S h ⟨i + 1, hi⟩ :=
  pair12ExactReturn_adjacent_ne S h hi

example (S : CyclicStaircase) (h : Pair13PlaneExact S)
    {i : ℕ} (hi : i + 1 < pair13Count S.D) :
    pair13ExactReturn S h ⟨i, by omega⟩ ≠
      pair13ExactReturn S h ⟨i + 1, hi⟩ :=
  pair13ExactReturn_adjacent_ne S h hi

example (S : CyclicStaircase) (h : Pair23PlaneExact S)
    {i : ℕ} (hi : i + 1 < pair23Count S.D) :
    pair23ExactReturn S h ⟨i, by omega⟩ ≠
      pair23ExactReturn S h ⟨i + 1, hi⟩ :=
  pair23ExactReturn_adjacent_ne S h hi

end

end NSP3
