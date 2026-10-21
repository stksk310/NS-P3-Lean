import NSP3.SharpTarget

namespace NSP3

example : quarterSquareCeil 0 = 0 := by native_decide
example : quarterSquareCeil 1 = 1 := by native_decide
example : quarterSquareCeil 2 = 1 := by native_decide
example : quarterSquareCeil 3 = 3 := by native_decide
example : quarterSquareCeil 4 = 4 := by native_decide
example : quarterSquareCeil 5 = 7 := by native_decide

example (k : ℕ) : quarterSquareCeil (2 * k) = k * k :=
  quarterSquareCeil_even k

example (k : ℕ) : quarterSquareCeil (2 * k + 1) = k * k + k + 1 :=
  quarterSquareCeil_odd k

example (S : CyclicStaircase) :
    noFullTarget S =
      ((pair12Count S.D + pair13Count S.D + pair23Count S.D + 1) ^ 2 + 3) / 4 := by
  simp [noFullTarget, quarterSquareCeil, pow_two]

end NSP3
