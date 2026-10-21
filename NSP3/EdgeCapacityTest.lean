import NSP3.EdgeCapacity

namespace NSP3

#check cyclicEdgeCapacity
#check edgeForm_of_commonResidue
#check allPositiveEdgeSpan
#check allNegativeEdgeSpan

example : 5 ≤ 2 * 4 - 4 + 1 := by
  let c : Fin 4 → ℕ := ![2, 4, 1, 3]
  apply cyclicEdgeCapacity c (R := 4) (h := 5) (d := 2)
  · norm_num
  · intro i; fin_cases i <;> norm_num [c]
  · intro i; fin_cases i <;> norm_num [c]
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [c]
  · norm_num
  · norm_num
  · intro i; fin_cases i <;> simp [c, edgeLeft, edgeRight] <;> omega
  · exact ⟨⟨0, by norm_num⟩, by simp [c, edgeLeft, edgeRight]⟩
  · exact ⟨⟨1, by norm_num⟩, by simp [c, edgeLeft, edgeRight]⟩

example : 2 * (4 - 1) ≤ 7 - 1 := by
  let c : Fin 4 → ℕ := ![1, 3, 5, 7]
  apply allPositiveEdgeSpan c (D := 2)
  · norm_num
  · intro i; fin_cases i <;> norm_num [c]
  · intro i; fin_cases i <;> norm_num [c]
  · intro i; fin_cases i <;> simp [c, edgeLeft, edgeRight] <;> omega

example : 2 * (4 - 1) ≤ 7 - 1 := by
  let c : Fin 4 → ℕ := ![7, 5, 3, 1]
  apply allNegativeEdgeSpan c (D := 2)
  · norm_num
  · intro i; fin_cases i <;> norm_num [c]
  · intro i; fin_cases i <;> norm_num [c]
  · intro i; fin_cases i <;> simp [c, edgeLeft, edgeRight] <;> omega

end NSP3
