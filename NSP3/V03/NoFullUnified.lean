import NSP3.UnbalancedResiduals
import NSP3.BalancedArithmetic

/-!
V03 unified no-full proof.  The unbounded t≥5 branch is proved once for
s≤r, rather than routed through the old strict/balanced case theorems.
The balanced residual widths 2,3,4 use fresh direct arithmetic.
-/
namespace NSP3.V03

set_option maxHeartbeats 4000000

private theorem two_mul_choose_two_strict (n : ℕ) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' n.two_dvd_mul_sub_one

private theorem quarterSquareCeil_le_of_lt (n b : ℕ)
    (h : n * n + 3 < (b + 1) * 4) : quarterSquareCeil n ≤ b := by
  unfold quarterSquareCeil
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul] <;> omega

private theorem pred_add_one_eq {n : ℕ} (h : 1 ≤ n) : n - 1 + 1 = n := by omega

private theorem mul_pred_add_self (n : ℕ) (h : 1 ≤ n) :
    n * (n - 1) + n = n * n := by
  cases n with
  | zero => omega
  | succ n => simp [Nat.succ_sub_one]; ring

private theorem simplexCard_large_lower (s t : ℕ) (ht : 5 ≤ t) (hts : t ≤ s) :
    (t - 1) * s - t + 5 ≤ simplexCard s t := by
  have hsimp := six_mul_simplexCard s t hts
  let u := s - t
  let v := t - 5
  let L := (t - 1) * s - t + 5
  have hu : u + t = s := by dsimp [u]; omega
  have hv : v + 5 = t := by dsimp [v]; omega
  have hL : L + t = (t - 1) * s + 5 := by
    dsimp [L]
    have hm : s ≤ (t - 1) * s := Nat.le_mul_of_pos_left s (by omega)
    have : t ≤ (t - 1) * s + 5 := by omega
    omega
  have hLplus : L + v = (t - 1) * s := by omega
  have htm1 : t - 1 = v + 4 := by omega
  have htm2 : t - 2 = v + 3 := by omega
  have hsq : t * t - t + 6 = t * (t - 1) + 6 := by
    have hm := mul_pred_add_self t (by omega)
    have hsub : (t * t - t) + t = t * t :=
      Nat.sub_add_cancel (Nat.le_mul_of_pos_left t (by omega))
    omega
  have hfac : 3 * s - 2 * t + 1 = 3 * u + t + 1 := by
    dsimp [u]
    omega
  have hfactor :
      t * (t - 1) * (3 * s - 2 * t + 1) =
        6 * L + v * (t * t - t + 6) + 3 * u * (t - 1) * (t - 2) := by
    rw [htm1, htm2, hsq, hfac]
    have hLuv : L + v = (v + 4) * (u + (v + 5)) := by
      rw [hLplus, htm1, ← hu, ← hv]
    calc
      t * (v + 4) * (3 * u + t + 1) =
          6 * (L + v) + v * t * (v + 4) + 3 * u * (v + 4) * (v + 3) := by
        rw [hLuv, ← hv]
        ring
      _ = 6 * L + v * (t * (v + 4) + 6) + 3 * u * (v + 4) * (v + 3) := by ring
      _ = 6 * L + v * (t * (t - 1) + 6) + 3 * u * (v + 4) * (v + 3) := by
        rw [htm1]
  have hp : 0 ≤ v * (t * t - t + 6) := Nat.zero_le _
  have hq : 0 ≤ 3 * u * (t - 1) * (t - 2) := Nat.zero_le _
  change L ≤ simplexCard s t
  nlinarith only [hsimp, hfactor, hp, hq]

private theorem unifiedTarget_le_m5_large_aux (r s t : ℕ)
    (ht : 5 ≤ t) (hts : t ≤ s) (hsr : s ≤ r) :
    quarterSquareCeil (r + s + t + 1) ≤
      strictM5 r s t + ((t - 1) * s - t + 5) := by
  apply quarterSquareCeil_le_of_lt
  have hr := two_mul_choose_two_strict r
  have hs' := two_mul_choose_two_strict s
  have ht' := two_mul_choose_two_strict t
  have hrr := mul_pred_add_self r (by omega)
  have hss := mul_pred_add_self s (by omega)
  have htt := mul_pred_add_self t (by omega)
  have hrc : 2 * Nat.choose r 2 + r = r * r := by omega
  have hsc : 2 * Nat.choose s 2 + s = s * s := by omega
  have htc : 2 * Nat.choose t 2 + t = t * t := by omega
  have hL : (((t - 1) * s - t + 5) + t) = (t - 1) * s + 5 := by
    have hm : s ≤ (t - 1) * s := Nat.le_mul_of_pos_left s (by omega)
    have : t ≤ (t - 1) * s + 5 := by omega
    omega
  have htsprod : (t - 1) * s + s = t * s := by
    calc
      (t - 1) * s + s = ((t - 1) + 1) * s := by ring
      _ = t * s := by rw [Nat.sub_add_cancel (by omega : 1 ≤ t)]
  have hB :
      2 * (3 * r + Nat.choose r 2 + Nat.choose s 2 + Nat.choose t 2 +
          ((t - 1) * s - t + 5) + 1) + r + s + t =
        6 * r + r * r + s * s + t * t +
          2 * ((t - 1) * s - t + 5) + 2 := by
    omega
  let d := r - s
  have hd : d + s = r := by dsimp [d]; omega
  have ht4 : 4 ≤ t := by omega
  simp only [strictM5]
  rcases le_total d (t - 4) with hle | hge
  · let e := t - 4 - d
    have he : e + d + 4 = t := by dsimp [e]; omega
    have he2 : 0 ≤ e * e := Nat.zero_le _
    have hid :
        (r + s + t + 1) * (r + s + t + 1) + 3 + (e * e + 4) =
          (3 * r + Nat.choose r 2 + Nat.choose s 2 + Nat.choose t 2 +
              ((t - 1) * s - t + 5) + 1) * 4 := by
      nlinarith only [hB, hL, htsprod, hd, he]
    omega
  · let e := d - (t - 4)
    have he : e + (t - 4) = d := by dsimp [e]; omega
    have he2 : 0 ≤ e * e := Nat.zero_le _
    have ht4eq : (t - 4) + 4 = t := by omega
    have hid :
        (r + s + t + 1) * (r + s + t + 1) + 3 + (e * e + 4) =
          (3 * r + Nat.choose r 2 + Nat.choose s 2 + Nat.choose t 2 +
              ((t - 1) * s - t + 5) + 1) * 4 := by
      nlinarith only [hB, hL, htsprod, hd, he, ht4eq]
    omega


/-- V03 common arithmetic range, allowing equality s=r. -/
theorem noFull_large_arithmetic (r s t : ℕ)
    (ht : 5 ≤ t) (hts : t ≤ s) (hsr : s ≤ r) :
    quarterSquareCeil (r+s+t+1) ≤ strictM5 r s t + simplexCard s t := by
  exact (unifiedTarget_le_m5_large_aux r s t ht hts hsr).trans
    (Nat.add_le_add_left (simplexCard_large_lower s t ht hts) _)

/-- The existing disjoint resources, with one common baseline in both cases. -/
theorem noFull_simplex_budget (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (ho : PairCountsOrdered S) :
    strictM5 (pair12Count S.D) (pair13Count S.D) (pair23Count S.D) +
      simplexCard (pair13Count S.D) (pair23Count S.D) ≤ S.m := by
  rcases lt_or_eq_of_le ho.2 with hlt | heq
  · simpa [strictM5] using m5_simplex_lower_strict S hnf ho hlt
  · have hb := m5_simplex_lower_equal S hnf ho heq.symm
    unfold strictM5
    omega

/-- The manuscript's single t≥5 route under the actual staircase hypotheses. -/
theorem noFull_large (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (ho : PairCountsOrdered S)
    (ht : 5 ≤ pair23Count S.D) : noFullTarget S ≤ S.m := by
  have ha := noFull_large_arithmetic (pair12Count S.D) (pair13Count S.D)
    (pair23Count S.D) ht ho.1 ho.2
  exact ha.trans (noFull_simplex_budget S hnf ho)

/-- V03's three-row balanced arithmetic table; no parity polynomial theorem. -/
theorem balanced_small_arithmetic (R t : ℕ)
    (ht : 2 ≤ t) (ht4 : t ≤ 4) (htr : t ≤ R) :
    quarterSquareCeil (R+R+t+1) ≤
      3*R+1+Nat.choose R 2+Nat.choose R 2+Nat.choose t 2+
      simplexCard R t+2 := by
  have hc := two_mul_choose_two_strict R
  have hp := mul_pred_add_self R (by omega)
  have hchoose : 2*Nat.choose R 2+R=R*R := by omega
  have hsimp := six_mul_simplexCard R t htr
  have hfactor : (3*R-2*t+1)+2*t=3*R+1 := by omega
  interval_cases t
  · have harg : R+R+2+1=2*(R+1)+1 := by omega
    rw [harg,quarterSquareCeil_odd]
    norm_num at hsimp hfactor ⊢
    nlinarith only [hchoose,hsimp,hfactor]
  · have harg : R+R+3+1=2*(R+2) := by omega
    rw [harg,quarterSquareCeil_even]
    norm_num at hsimp hfactor ⊢
    nlinarith only [hchoose,hsimp,hfactor,htr]
  · have harg : R+R+4+1=2*(R+2)+1 := by omega
    rw [harg,quarterSquareCeil_odd]
    rw [show Nat.choose 4 2=6 from by decide]
    norm_num at hsimp hfactor ⊢
    nlinarith only [hchoose,hsimp,hfactor,htr]

private theorem noFull_balanced_small (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (ho : PairCountsOrdered S)
    (heq : pair12Count S.D=pair13Count S.D)
    (ht4 : pair23Count S.D≤4) : noFullTarget S≤S.m := by
  let R := pair13Count S.D
  let t := pair23Count S.D
  have htr : t≤R := ho.1
  have hb := m5_lower_equal S ho heq
  have hbR : 3*R+1+Nat.choose R 2+Nat.choose R 2+Nat.choose t 2≤S.m := by
    simpa [R,t,heq] using hb
  have htarget : noFullTarget S=quarterSquareCeil (R+R+t+1) := by
    simp [noFullTarget,R,t,heq]
  rw [htarget]
  by_cases ht0 : t=0
  · simpa [ht0] using (balancedTarget_le_m5_t0 R).trans (by simpa [ht0] using hbR)
  by_cases ht1 : t=1
  · simpa [ht1] using (balancedTarget_le_m5_t1 R).trans (by simpa [ht1] using hbR)
  have ht2 : 2≤t := by omega
  have ha := balanced_small_arithmetic R t ht2 (by simpa [t] using ht4) htr
  have hb2 := noFull_balanced_plus_two S hnf ho heq (by simpa [t] using ht2)
  have hb2R : 3*R+1+Nat.choose R 2+Nat.choose R 2+Nat.choose t 2+
      simplexCard R t+2≤S.m := by simpa [R,t,heq] using hb2
  exact ha.trans hb2R

private theorem noFull_unbalanced_small (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (hlt : pair13Count S.D < pair12Count S.D)
    (htle : pair23Count S.D ≤ 4) :
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
  · have htbound : t ≤ 4 := by simpa [t] using htle
    omega


/-- The V03 no-full theorem: common large range, then only t≤4 residues. -/
theorem noFull_unified (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (ho : PairCountsOrdered S) :
    noFullTarget S≤S.m := by
  by_cases ht : 5≤pair23Count S.D
  · exact noFull_large S hnf ho ht
  have ht4 : pair23Count S.D≤4 := by omega
  rcases lt_or_eq_of_le ho.2 with hlt | heq
  · exact noFull_unbalanced_small S hnf ho hlt ht4
  · exact noFull_balanced_small S hnf ho heq.symm ht4

end NSP3.V03
