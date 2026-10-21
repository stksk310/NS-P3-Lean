import NSP3.ReturnSpacing

namespace NSP3


example (S : CyclicStaircase) (h : Pair12PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair12Count S.D)
    (hlt : pair12ExactReturn S h ⟨i, by omega⟩ <
      pair12ExactReturn S h ⟨i + 1, hi⟩) :
    pair23Count S.D ≤
      pair12ExactReturn S h ⟨i + 1, hi⟩ - pair12ExactReturn S h ⟨i, by omega⟩ :=
  pair12ExactReturn_step_up S h hi hlt

example (S : CyclicStaircase) (h : Pair12PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair12Count S.D)
    (hlt : pair12ExactReturn S h ⟨i + 1, hi⟩ <
      pair12ExactReturn S h ⟨i, by omega⟩) :
    pair13Count S.D ≤
      pair12ExactReturn S h ⟨i, by omega⟩ - pair12ExactReturn S h ⟨i + 1, hi⟩ :=
  pair12ExactReturn_step_down S h hi hlt

example (S : CyclicStaircase) (h : Pair13PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair13Count S.D)
    (hlt : pair13ExactReturn S h ⟨i, by omega⟩ <
      pair13ExactReturn S h ⟨i + 1, hi⟩) :
    pair23Count S.D ≤
      pair13ExactReturn S h ⟨i + 1, hi⟩ - pair13ExactReturn S h ⟨i, by omega⟩ :=
  pair13ExactReturn_step_up S h hi hlt

example (S : CyclicStaircase) (h : Pair13PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair13Count S.D)
    (hlt : pair13ExactReturn S h ⟨i + 1, hi⟩ <
      pair13ExactReturn S h ⟨i, by omega⟩) :
    pair12Count S.D ≤
      pair13ExactReturn S h ⟨i, by omega⟩ - pair13ExactReturn S h ⟨i + 1, hi⟩ :=
  pair13ExactReturn_step_down S h hi hlt

example (S : CyclicStaircase) (h : Pair23PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair23Count S.D)
    (hlt : pair23ExactReturn S h ⟨i, by omega⟩ <
      pair23ExactReturn S h ⟨i + 1, hi⟩) :
    pair13Count S.D ≤
      pair23ExactReturn S h ⟨i + 1, hi⟩ - pair23ExactReturn S h ⟨i, by omega⟩ :=
  pair23ExactReturn_step_up S h hi hlt

example (S : CyclicStaircase) (h : Pair23PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair23Count S.D)
    (hlt : pair23ExactReturn S h ⟨i + 1, hi⟩ <
      pair23ExactReturn S h ⟨i, by omega⟩) :
    pair12Count S.D ≤
      pair23ExactReturn S h ⟨i, by omega⟩ - pair23ExactReturn S h ⟨i + 1, hi⟩ :=
  pair23ExactReturn_step_down S h hi hlt

end NSP3
