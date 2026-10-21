import NSP3.BalancedArithmetic

namespace NSP3

theorem noFull_balanced_sharp (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D) :
    noFullTarget S ≤ S.m := by
  let R := pair13Count S.D
  let t := pair23Count S.D
  have htr : t ≤ R := hord.1
  have hm5 := m5_lower_equal S hord heq
  have hm5R :
      3 * R + 1 + Nat.choose R 2 + Nat.choose R 2 + Nat.choose t 2 ≤ S.m := by
    simpa [R, t, heq] using hm5
  have htarget : noFullTarget S = quarterSquareCeil (R + R + t + 1) := by
    simp [noFullTarget, R, t, heq]
  rw [htarget]
  rcases lt_trichotomy t 1 with ht0 | ht1 | ht2
  · have htzero : t = 0 := by omega
    have harith := balancedTarget_le_m5_t0 R
    have hm50 := hm5R
    rw [htzero] at hm50 ⊢
    exact harith.trans hm50
  · have htone : t = 1 := ht1
    have harith := balancedTarget_le_m5_t1 R
    have hm51 := hm5R
    rw [htone] at hm51 ⊢
    exact harith.trans hm51
  · have ht : 2 ≤ t := by omega
    have harith := balancedTarget_le_m5_simplex_plus_two R t ht htr
    have hcard := noFull_balanced_plus_two S hnf hord heq ht
    have hcardR : 3 * R + 1 + Nat.choose R 2 + Nat.choose R 2 + Nat.choose t 2
        + simplexCard R t + 2 ≤ S.m := by
      simpa [R, t, heq] using hcard
    exact harith.trans hcardR

end NSP3
