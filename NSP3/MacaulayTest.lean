import NSP3.Macaulay
namespace NSP3
example (r n : ℕ) (hr : 0 < r) : n ≤ macaulayRaise r n := macaulayRaise_ge r n hr
example (r : ℕ) : macaulayRaise r 0 = 0 := macaulayRaise_zero r
example (r n : ℕ) (hr : 0 < r) : binomialValue r (macaulayDigits r n) = n :=
  macaulayDigits_reconstruct r n hr
example (r n : ℕ) : MacaulayValid r (macaulayDigits r n) := macaulayDigits_valid r n
example (r n : ℕ) (ds : List ℕ) (hv : MacaulayValid r ds) (hn : binomialValue r ds = n) :
    ds = macaulayDigits r n := macaulayExpansion_unique r n ds hv hn
example : macaulayDigits 2 5 = [3, 2] := by decide
example : macaulayDigits 3 9 = [4, 3, 2] := by decide
example : (List.range 6).map (macaulayRaise 2) = [0, 1, 2, 4, 5, 7] := by decide
example : (List.range 10).map (macaulayRaise 3) = [0, 1, 2, 3, 5, 6, 7, 9, 10, 12] := by decide
example : MacaulayValid 3 [4, 3, 2] := by simp [MacaulayValid]
example : ¬ MacaulayValid 3 [4, 4] := by simp [MacaulayValid]
example : ¬ MacaulayValid 3 [2] := by simp [MacaulayValid]
end NSP3

