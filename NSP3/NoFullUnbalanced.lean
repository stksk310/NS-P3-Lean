import NSP3.UnbalancedResiduals
import NSP3.NoFullBalanced

namespace NSP3

theorem noFull_unbalanced_sharp (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (hlt : pair13Count S.D < pair12Count S.D) :
    noFullTarget S ≤ S.m := by
  let r := pair12Count S.D
  let s := pair13Count S.D
  let t := pair23Count S.D
  have hts : t ≤ s := by exact hord.1
  have hsr : s < r := by exact hlt
  have hm5 : strictM5 r s t ≤ S.m := by
    simpa [strictM5, r, s, t] using m5_lower_strict S hord hlt
  have htarget : noFullTarget S = quarterSquareCeil (r + s + t + 1) := by
    simp [noFullTarget, r, s, t]
  rw [htarget]
  by_cases ht01 : t ≤ 1
  · exact (unbalancedTarget_le_m5_small_t r s t hsr ht01).trans hm5
  have ht2 : 2 ≤ t := by omega
  by_cases heq2 : t = 2
  · by_cases hd2 : 2 ≤ r - s
    · have harith := unbalancedTarget_le_m5_t2_core r s (by omega) hd2
      have hcore := fullCore_card_lower_t2 S hlt (by simpa [t] using heq2)
      have hbudget : strictM5 r s 2 + (s - 1) ≤ S.m := by
        have hfull := m5_fullCore_lower_strict S hnf hord hlt
        have hfull' : strictM5 r s 2 + (fullCoreFinset S).card ≤ S.m := by
          simpa [strictM5, r, s, t, heq2] using hfull
        exact (Nat.add_le_add_left hcore _).trans hfull'
      simpa [heq2] using harith.trans hbudget
    · have hsucc : pair12Count S.D = pair13Count S.D + 1 := by
        dsimp [r, s] at hd2 hsr ⊢
        omega
      have hres := noFull_residual_succ_s_2 S hnf hord hsucc (by simpa [t] using heq2)
      rw [htarget] at hres
      exact hres
  by_cases heq3 : t = 3
  · by_cases hregular : 2 ≤ r - s ∨ 5 ≤ s
    · have harith := unbalancedTarget_le_m5_t3_core r s (by omega) hsr hregular
      have hcore := fullCore_card_lower_t3 S hord hlt (by simpa [t] using heq3)
      have hbudget : strictM5 r s 3 + (3 * s - 4) ≤ S.m := by
        have hfull := m5_fullCore_lower_strict S hnf hord hlt
        have hfull' : strictM5 r s 3 + (fullCoreFinset S).card ≤ S.m := by
          simpa [strictM5, r, s, t, heq3] using hfull
        exact (Nat.add_le_add_left hcore _).trans hfull'
      simpa [heq3] using harith.trans hbudget
    · have hd1 : r = s + 1 := by omega
      have hslt5 : s < 5 := by omega
      have hs3 : 3 ≤ s := by omega
      have hsCases : s = 3 ∨ s = 4 := by omega
      rcases hsCases with hsEq | hsEq
      · have hres := noFull_residual_433 S hnf hord (by
            dsimp [r, s] at hd1 hsEq
            omega)
          (by simpa [s] using hsEq) (by simpa [t] using heq3)
        rw [htarget] at hres
        exact hres
      · have hres := noFull_residual_543 S hnf hord (by
            dsimp [r, s] at hd1 hsEq
            omega)
          (by simpa [s] using hsEq) (by simpa [t] using heq3)
        rw [htarget] at hres
        exact hres
  by_cases heq4 : t = 4
  · have hs4 : 4 ≤ s := by omega
    by_cases hs5 : 5 ≤ s
    · have harith := unbalancedTarget_le_m5_t4_simplex r s hs5 hsr
      have hsimplex := m5_simplex_lower_strict S hnf hord hlt
      have hbudget : strictM5 r s 4 + simplexCard s 4 ≤ S.m := by
        simpa [strictM5, r, s, t, heq4] using hsimplex
      simpa [heq4] using harith.trans hbudget
    · have hsEq : s = 4 := by omega
      by_cases hr5 : r = 5
      · have harith := unbalancedTarget_le_m5_544
        have hcore := fullCore_card_lower_544 S (by simpa [r] using hr5)
          (by simpa [s] using hsEq) (by simpa [t] using heq4)
        have hfull := m5_fullCore_lower_strict S hnf hord hlt
        have hbudget : strictM5 5 4 4 + 13 ≤ S.m := by
          have hfull' : strictM5 5 4 4 + (fullCoreFinset S).card ≤ S.m := by
            simpa [strictM5, r, s, t, hr5, hsEq, heq4] using hfull
          exact (Nat.add_le_add_left hcore _).trans hfull'
        simpa [hr5, hsEq, heq4] using harith.trans hbudget
      · have hr6 : 6 ≤ r := by omega
        have harith := unbalancedTarget_le_m5_44_large r hr6
        have hcore := fullCore_card_lower_44_large S (by simpa [r] using hr6)
          (by simpa [s] using hsEq) (by simpa [t] using heq4)
        have hfull := m5_fullCore_lower_strict S hnf hord hlt
        have hbudget : strictM5 r 4 4 + 14 ≤ S.m := by
          have hfull' : strictM5 r 4 4 + (fullCoreFinset S).card ≤ S.m := by
            simpa [strictM5, r, s, t, hsEq, heq4] using hfull
          exact (Nat.add_le_add_left hcore _).trans hfull'
        simpa [hsEq, heq4] using harith.trans hbudget
  · have ht5 : 5 ≤ t := by omega
    have harith := unbalancedTarget_le_m5_simplex_large r s t ht5 hts hsr
    have hsimplex := m5_simplex_lower_strict S hnf hord hlt
    have hbudget : strictM5 r s t + simplexCard s t ≤ S.m := by
      simpa [strictM5, r, s, t] using hsimplex
    exact harith.trans hbudget

theorem noFull_sharp_bound_ordered (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S) :
    noFullTarget S ≤ S.m := by
  rcases lt_or_eq_of_le hord.2 with hlt | heq
  · exact noFull_unbalanced_sharp S hnf hord hlt
  · exact noFull_balanced_sharp S hnf hord heq.symm

end NSP3
