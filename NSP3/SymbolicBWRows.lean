import NSP3.SymbolicBWCore

namespace NSP3

theorem coreCardRows_mono_first (r r' s t : ℕ) (h : r ≤ r') :
    coreCardRows r s t ≤ coreCardRows r' s t := by
  unfold coreCardRows
  apply Finset.sum_le_sum
  intro y hy
  apply Finset.sum_le_sum
  intro z hz
  split_ifs
  · exact min_le_min (Nat.sub_le_sub_right h y) le_rfl
  · exact le_rfl

theorem coreCardRows_t4_card (r s : ℕ) (hs : 4 ≤ s) (hr : s ≤ r) :
    6*s = coreCardRows r s 4+
      (if r=s then 13 else if r=s+1 then 11 else 10) := by
  have he : Finset.Icc 1 4 = {1,2,3,4} := by decide
  have h11 : min (r-1) (s-1)=s-1 := min_eq_right (by omega)
  have h12 : min (r-1) (s-2)=s-2 := min_eq_right (by omega)
  have h13 : min (r-1) (s-3)=s-3 := min_eq_right (by omega)
  have h22 : min (r-2) (s-2)=s-2 := min_eq_right (by omega)
  unfold coreCardRows
  norm_num [he,h11,h12,h13,h22]
  split_ifs <;> omega

theorem coreCardRows_t5_lower (r s : ℕ) (hs : 5 ≤ s) (hr : s ≤ r) :
    10*s ≤ coreCardRows r s 5+27 := by
  have hm := coreCardRows_mono_first s r s 5 hr
  have he : Finset.Icc 1 5 = {1,2,3,4,5} := by decide
  have hmin (y z : ℕ) : min (s-y) (s-z)=s-max y z := by omega
  have hb : 10*s = coreCardRows s s 5+27 := by
    unfold coreCardRows
    simp_rw [hmin]
    norm_num [he]
    omega
  omega

theorem coreCardRows_t5_strict_lower (r s : ℕ) (hs : 5 ≤ s) (hr : s+1 ≤ r) :
    10*s ≤ coreCardRows r s 5+23 := by
  have hm := coreCardRows_mono_first (s+1) r s 5 hr
  have he : Finset.Icc 1 5 = {1,2,3,4,5} := by decide
  have hmin (y z : ℕ) : min (s+1-y) (s-z)=s-max (y-1) z := by omega
  have hb : 10*s = coreCardRows (s+1) s 5+23 := by
    unfold coreCardRows
    simp_rw [hmin]
    norm_num [he]
    omega
  omega

theorem coreCardRows_t6_lower (r s : ℕ) (hs : 6 ≤ s) (hr : s ≤ r) :
    15*s ≤ coreCardRows r s 6+48 := by
  have hm := coreCardRows_mono_first s r s 6 hr
  have he : Finset.Icc 1 6 = {1,2,3,4,5,6} := by decide
  have hmin (y z : ℕ) : min (s-y) (s-z)=s-max y z := by omega
  have hb : 15*s = coreCardRows s s 6+48 := by
    unfold coreCardRows
    simp_rw [hmin]
    norm_num [he]
    omega
  omega

end NSP3
