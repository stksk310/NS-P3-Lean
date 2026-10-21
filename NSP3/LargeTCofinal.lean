import NSP3.PuncturedSimplexBudget
import NSP3.FullDeficit

namespace NSP3

private theorem six_mul_choose_three (h : ℕ) (hh : 3 ≤ h) :
    6 * Nat.choose h 3 = h * (h - 1) * (h - 2) := by
  have hc := Nat.descFactorial_eq_factorial_mul_choose h 3
  norm_num [Nat.descFactorial] at hc
  have h1 : h - 1 + 1 = h := by omega
  have h2 : h - 2 + 2 = h := by omega
  nlinarith

private theorem large_margin_ge_eight (s t : ℕ) (ht : 8 ≤ t) (hts : t ≤ s) :
    s * t + 3 + largeHoleCap t < simplexCard s t := by
  have hsimp := six_mul_simplexCard s t hts
  let h := (t + 2) / 2
  have hh : 3 ≤ h := by dsimp [h]; omega
  have hcap := six_mul_choose_three h hh
  change 6 * largeHoleCap t = h * (h - 1) * (h - 2) at hcap
  let d := s - t
  have hsd : d + t = s := by dsimp [d]; omega
  obtain ⟨n, hn | hn⟩ := Nat.even_or_odd' t
  · have hn4 : 4 ≤ n := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn4
    have hhval : h = n + 1 := by dsimp [h]; omega
    have hpoly : 24 * n ^ 2 + n + 18 < 7 * n ^ 3 := by
      rw [hk]
      ring_nf
      omega
    have hdpos : 0 ≤ 3 * t * (t - 3) * d := Nat.zero_le _
    rw [hn, ← hsd] at hsimp ⊢
    rw [hn, hhval] at hcap
    have hfac : 3 * (d + t) - 2 * (2 * n) + 1 = 3 * d + 2 * n + 1 := by
      omega
    have hc1 : n + 1 - 1 = n := by omega
    have hc2 : n + 1 - 2 = n - 1 := by omega
    rw [hfac] at hsimp
    rw [hc1, hc2] at hcap
    rw [hn] at hsimp ⊢
    have hextra : 0 ≤ 6 * n * (2 * n - 3) * d := Nat.zero_le _
    let e := 7 * n ^ 3 - (24 * n ^ 2 + n + 18)
    have hepos : 0 < e := by dsimp [e]; omega
    have heq : e + (24 * n ^ 2 + n + 18) = 7 * n ^ 3 := by
      dsimp [e]; omega
    have hid : 6 * ((d + 2 * n) * (2 * n) + 3 + largeHoleCap (2 * n)) +
        e + 6 * n * (2 * n - 3) * d =
        6 * simplexCard (d + 2 * n) (2 * n) := by
      rw [hsimp]
      rw [hk] at hcap heq ⊢
      have hk3 : 2 * (4 + k) - 3 = 5 + k * 2 := by omega
      have hk1 : 2 * (4 + k) - 1 = 7 + k * 2 := by omega
      rw [hk3, hk1]
      norm_num at hcap ⊢
      ring_nf at hcap heq ⊢
      linear_combination hcap + heq
    omega
  · have hn4 : 4 ≤ n := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn4
    have hhval : h = n + 1 := by dsimp [h]; omega
    have hpoly : 12 * n ^ 2 + 19 * n + 24 < 7 * n ^ 3 := by
      rw [hk]
      ring_nf
      omega
    have hdpos : 0 ≤ 3 * t * (t - 3) * d := Nat.zero_le _
    rw [hn, ← hsd] at hsimp ⊢
    rw [hn, hhval] at hcap
    have htm : 2 * n + 1 - 1 = 2 * n := by omega
    have hfac : 3 * (d + t) - 2 * (2 * n + 1) + 1 =
        3 * d + 2 * n + 2 := by omega
    have hc1 : n + 1 - 1 = n := by omega
    have hc2 : n + 1 - 2 = n - 1 := by omega
    rw [htm, hfac] at hsimp
    rw [hc1, hc2] at hcap
    rw [hn] at hsimp ⊢
    have hextra : 0 ≤ 3 * (2 * n + 1) * (2 * n - 2) * d := Nat.zero_le _
    let e := 7 * n ^ 3 - (12 * n ^ 2 + 19 * n + 24)
    have hepos : 0 < e := by dsimp [e]; omega
    have heq : e + (12 * n ^ 2 + 19 * n + 24) = 7 * n ^ 3 := by
      dsimp [e]; omega
    have hid : 6 * ((d + (2 * n + 1)) * (2 * n + 1) + 3 +
        largeHoleCap (2 * n + 1)) + e +
        3 * (2 * n + 1) * (2 * n - 2) * d =
        6 * simplexCard (d + (2 * n + 1)) (2 * n + 1) := by
      rw [hsimp]
      rw [hk] at hcap heq ⊢
      have hk2 : 2 * (4 + k) - 2 = 6 + k * 2 := by omega
      rw [hk2]
      norm_num at hcap ⊢
      ring_nf at hcap heq ⊢
      linear_combination hcap + heq
    omega

private theorem margin_t4 (s : ℕ) (hs : 10 ≤ s) :
    s * 4 + 3 + largeHoleCap 4 < simplexCard s 4 := by
  have h := six_mul_simplexCard s 4 (by omega)
  norm_num [largeHoleCap] at ⊢
  norm_num at h
  omega

private theorem margin_t5 (s : ℕ) (hs : 7 ≤ s) :
    s * 5 + 3 + largeHoleCap 5 < simplexCard s 5 := by
  have h := six_mul_simplexCard s 5 (by omega)
  norm_num [largeHoleCap] at ⊢
  norm_num at h
  omega

private theorem margin_t6 (s : ℕ) (hs : 7 ≤ s) :
    s * 6 + 3 + largeHoleCap 6 < simplexCard s 6 := by
  have h := six_mul_simplexCard s 6 (by omega)
  norm_num [largeHoleCap] at ⊢
  norm_num at h
  omega

private theorem margin_t7 (s : ℕ) (hs : 8 ≤ s) :
    s * 7 + 3 + largeHoleCap 7 < simplexCard s 7 := by
  have h := six_mul_simplexCard s 7 (by omega)
  norm_num [largeHoleCap] at ⊢
  norm_num at h
  omega

private theorem exceptional_494 (r : ℕ) (hr : 9 ≤ r)
    (hsq : ((r : ℤ) - 9 - 4 + 3) ^ 2 ≤ 4 * (9 : ℤ) * 4 + 12) :
    quarterSquareCeil (r + 9 + 4 + 2) + Nat.choose ((9 + 4 + 2 - r) / 2) 3 <
      3 * r + 1 + Nat.choose r 2 + Nat.choose 9 2 + Nat.choose 4 2 +
        simplexCard 9 4 := by
  have hupper : r ≤ 22 := by nlinarith
  interval_cases r <;> norm_num [quarterSquareCeil, simplexCard, Nat.choose] at *

private theorem exceptional_777 (r : ℕ) (hr : 7 ≤ r)
    (hsq : ((r : ℤ) - 7 - 7 + 3) ^ 2 ≤ 4 * (7 : ℤ) * 7 + 12) :
    quarterSquareCeil (r + 7 + 7 + 2) + Nat.choose ((7 + 7 + 2 - r) / 2) 3 <
      3 * r + 1 + Nat.choose r 2 + Nat.choose 7 2 + Nat.choose 7 2 +
        simplexCard 7 7 := by
  have hupper : r ≤ 25 := by nlinarith
  interval_cases r <;> norm_num [quarterSquareCeil, simplexCard, Nat.choose] at *

theorem fullSupport_large_t_strict (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S)
    (hregion :
      (pair23Count S.D = 4 ∧ 9 ≤ pair13Count S.D) ∨
      (pair23Count S.D = 5 ∧ 7 ≤ pair13Count S.D) ∨
      (pair23Count S.D = 6 ∧ 7 ≤ pair13Count S.D) ∨
      7 ≤ pair23Count S.D) :
    fullTarget S < S.m := by
  let r := pair12Count S.D
  let s := pair13Count S.D
  let t := pair23Count S.D
  have hts : t ≤ s := hord.1
  have hsr : s ≤ r := hord.2
  have htpos : 1 ≤ t := by rcases hregion with h | h | h | h <;> omega
  have hspos : 1 ≤ s := by omega
  have hrpos : 1 ≤ r := by omega
  have htarget := fullTarget_le_fullM_add_product S
  by_contra hnot
  have hmle : S.m ≤ fullTarget S := by omega
  rcases hregion with h4 | h5 | h6 | hlarge
  · rcases h4 with ⟨ht4eq, hs9⟩
    by_cases hs10 : 10 ≤ s
    · have hm := margin_t4 s hs10
      have hb := full_simplex_largeHole_budget S hg hfull hord
      dsimp [s, t] at hm
      rw [ht4eq] at hb htarget
      omega
    · have hsval : s = 9 := by omega
      have hsval' : pair13Count S.D = 9 := by simpa [s] using hsval
      have hM : fullM S ≤ fullTarget S := by
        have ha := full_resource_accounting S hg hfull
        omega
      have hsq := fullDeficit_square_bound S hM
      have ha := exceptional_494 r (by omega)
        (by simpa [s, t, hsval, hsval', ht4eq] using hsq)
      have hb := full_simplex_hole_budget S hg hfull hord
      have hh := coreHole_card_le_choose_height S hg hfull hord
      dsimp [r] at ha
      have hheight : coreHoleHeight S = (15 - pair12Count S.D) / 2 := by
        simp [coreHoleHeight, hsval', ht4eq]
      rw [hheight] at hh
      have ha' : fullTarget S + Nat.choose ((15 - pair12Count S.D) / 2) 3 <
          fullM S + simplexCard 9 4 := by
        simpa [fullTarget, fullM, hsval', ht4eq] using ha
      rw [hsval', ht4eq] at hb
      omega
  · rcases h5 with ⟨ht5eq, hs7⟩
    have hm := margin_t5 s hs7
    have hb := full_simplex_largeHole_budget S hg hfull hord
    dsimp [s, t] at hm
    rw [ht5eq] at hb htarget
    omega
  · rcases h6 with ⟨ht6eq, hs7⟩
    have hm := margin_t6 s hs7
    have hb := full_simplex_largeHole_budget S hg hfull hord
    dsimp [s, t] at hm
    rw [ht6eq] at hb htarget
    omega
  · by_cases ht8 : 8 ≤ t
    · have hm := large_margin_ge_eight s t ht8 hts
      have hb := full_simplex_largeHole_budget S hg hfull hord
      dsimp [s, t] at hm
      omega
    · have htval : t = 7 := by omega
      have htval' : pair23Count S.D = 7 := by simpa [t] using htval
      by_cases hs8 : 8 ≤ s
      · have hm := margin_t7 s hs8
        have hb := full_simplex_largeHole_budget S hg hfull hord
        dsimp [s, t] at hm
        rw [htval'] at hb htarget
        omega
      · have hsval : s = 7 := by omega
        have hsval' : pair13Count S.D = 7 := by simpa [s] using hsval
        have hM : fullM S ≤ fullTarget S := by
          have ha := full_resource_accounting S hg hfull
          omega
        have hsq := fullDeficit_square_bound S hM
        have ha := exceptional_777 r (by omega)
          (by simpa [s, t, hsval, htval, hsval', htval'] using hsq)
        have hb := full_simplex_hole_budget S hg hfull hord
        have hh := coreHole_card_le_choose_height S hg hfull hord
        dsimp [r] at ha
        have hheight : coreHoleHeight S = (16 - pair12Count S.D) / 2 := by
          simp [coreHoleHeight, hsval', htval']
        rw [hheight] at hh
        have ha' : fullTarget S + Nat.choose ((16 - pair12Count S.D) / 2) 3 <
            fullM S + simplexCard 7 7 := by
          simpa [fullTarget, fullM, hsval', htval'] using ha
        rw [hsval', htval'] at hb
        omega

end NSP3
