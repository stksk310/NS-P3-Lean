import NSP3.UnbalancedArithmetic

namespace NSP3

example (r s t : ℕ) (hst : s < r) (ht : t ≤ 1) :
    quarterSquareCeil (r + s + t + 1) ≤ strictM5 r s t :=
  unbalancedTarget_le_m5_small_t r s t hst ht

example (r s : ℕ) (hs : 2 ≤ s) (hd : 2 ≤ r - s) :
    quarterSquareCeil (r + s + 2 + 1) ≤ strictM5 r s 2 + (s - 1) :=
  unbalancedTarget_le_m5_t2_core r s hs hd

example (r s : ℕ) (hs : 3 ≤ s) (hst : s < r)
    (hregular : 2 ≤ r - s ∨ 5 ≤ s) :
    quarterSquareCeil (r + s + 3 + 1) ≤ strictM5 r s 3 + (3 * s - 4) :=
  unbalancedTarget_le_m5_t3_core r s hs hst hregular

example (r s : ℕ) (hs : 5 ≤ s) (hst : s < r) :
    quarterSquareCeil (r + s + 4 + 1) ≤ strictM5 r s 4 + simplexCard s 4 :=
  unbalancedTarget_le_m5_t4_simplex r s hs hst

example (r s t : ℕ) (ht : 5 ≤ t) (hts : t ≤ s) (hsr : s < r) :
    quarterSquareCeil (r + s + t + 1) ≤ strictM5 r s t + simplexCard s t :=
  unbalancedTarget_le_m5_simplex_large r s t ht hts hsr

example : quarterSquareCeil (5 + 4 + 4 + 1) ≤ strictM5 5 4 4 + 13 :=
  unbalancedTarget_le_m5_544

example (r : ℕ) (hr : 6 ≤ r) :
    quarterSquareCeil (r + 4 + 4 + 1) ≤ strictM5 r 4 4 + 14 :=
  unbalancedTarget_le_m5_44_large r hr

example (s : ℕ) (hs : 2 ≤ s) :
    quarterSquareCeil ((s + 1) + s + 2 + 1) = strictM5 (s + 1) s 2 + s :=
  unbalanced_residual_succ_s_2 s hs

-- Closed boundary instances requested by the L07 verification contract.
example : quarterSquareCeil (6 + 5 + 5 + 1) ≤
    strictM5 6 5 5 + simplexCard 5 5 := by
  exact unbalancedTarget_le_m5_simplex_large 6 5 5 (by omega) (by omega) (by omega)

example : quarterSquareCeil (6 + 4 + 4 + 1) ≤ strictM5 6 4 4 + 14 := by
  exact unbalancedTarget_le_m5_44_large 6 (by omega)

example : quarterSquareCeil (4 + 2 + 2 + 1) ≤ strictM5 4 2 2 + (2 - 1) := by
  exact unbalancedTarget_le_m5_t2_core 4 2 (by omega) (by omega)

example : quarterSquareCeil (5 + 3 + 3 + 1) ≤ strictM5 5 3 3 + (3 * 3 - 4) := by
  exact unbalancedTarget_le_m5_t3_core 5 3 (by omega) (by omega) (Or.inl (by omega))

example : quarterSquareCeil (4 + 3 + 3 + 1) = strictM5 4 3 3 + 7 :=
  unbalanced_residual_433

example : quarterSquareCeil (5 + 4 + 3 + 1) = strictM5 5 4 3 + 9 :=
  unbalanced_residual_543

end NSP3
