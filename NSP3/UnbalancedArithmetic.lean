import NSP3.StrictResources
import NSP3.NoFullResources
import NSP3.SimplexPolynomial

namespace NSP3

set_option maxHeartbeats 2000000

def strictM5 (r s t : ℕ) : ℕ :=
  3 * r + Nat.choose r 2 + Nat.choose s 2 + Nat.choose t 2

private theorem two_mul_choose_two_strict (n : ℕ) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  exact Nat.mul_div_cancel' n.two_dvd_mul_sub_one

private theorem quarterSquareCeil_le_of_lt (n b : ℕ)
    (h : n * n + 3 < (b + 1) * 4) : quarterSquareCeil n ≤ b := by
  unfold quarterSquareCeil
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul] <;> omega

theorem unbalancedTarget_le_m5_small_t (r s t : ℕ)
    (hst : s < r) (ht : t ≤ 1) :
    quarterSquareCeil (r + s + t + 1) ≤ strictM5 r s t := by
  apply quarterSquareCeil_le_of_lt
  have hr := two_mul_choose_two_strict r
  have hs := two_mul_choose_two_strict s
  have ht' := two_mul_choose_two_strict t
  unfold strictM5
  interval_cases t <;> norm_num at ht' ⊢
  · cases r with
    | zero => omega
    | succ r =>
      have hrsub : r + 1 - 1 = r := by omega
      rw [hrsub] at hr
      cases s with
      | zero => norm_num at hs ⊢; nlinarith
      | succ s =>
        simp only [Nat.succ_sub_one] at hr hs
        nlinarith
  · cases r with
    | zero => omega
    | succ r =>
      have hrsub : r + 1 - 1 = r := by omega
      rw [hrsub] at hr
      cases s with
      | zero => norm_num at hs ⊢; nlinarith
      | succ s =>
        simp only [Nat.succ_sub_one] at hr hs
        nlinarith

private theorem pred_add_one_eq {n : ℕ} (h : 1 ≤ n) : n - 1 + 1 = n := by omega

private theorem mul_pred_add_self (n : ℕ) (h : 1 ≤ n) :
    n * (n - 1) + n = n * n := by
  cases n with
  | zero => omega
  | succ n => simp [Nat.succ_sub_one]; ring

theorem unbalancedTarget_le_m5_t2_core (r s : ℕ)
    (hs : 2 ≤ s) (hd : 2 ≤ r - s) :
    quarterSquareCeil (r + s + 2 + 1) ≤ strictM5 r s 2 + (s - 1) := by
  apply quarterSquareCeil_le_of_lt
  have hr := two_mul_choose_two_strict r
  have hs' := two_mul_choose_two_strict s
  have hrp := pred_add_one_eq (by omega : 1 ≤ r)
  have hsp := pred_add_one_eq (by omega : 1 ≤ s)
  have hrr := mul_pred_add_self r (by omega)
  have hss := mul_pred_add_self s (by omega)
  have hrc : 2 * Nat.choose r 2 + r = r * r := by omega
  have hsc : 2 * Nat.choose s 2 + s = s * s := by omega
  have hc2 : Nat.choose 2 2 = 1 := by decide
  have hd' : s + 2 ≤ r := by omega
  simp only [strictM5, hc2]
  norm_num at ⊢
  nlinarith

theorem unbalancedTarget_le_m5_t3_core (r s : ℕ)
    (hs : 3 ≤ s) (hst : s < r)
    (hregular : 2 ≤ r - s ∨ 5 ≤ s) :
    quarterSquareCeil (r + s + 3 + 1) ≤ strictM5 r s 3 + (3 * s - 4) := by
  apply quarterSquareCeil_le_of_lt
  have hr := two_mul_choose_two_strict r
  have hs' := two_mul_choose_two_strict s
  have hrp := pred_add_one_eq (by omega : 1 ≤ r)
  have hsp := pred_add_one_eq (by omega : 1 ≤ s)
  have hrr := mul_pred_add_self r (by omega)
  have hss := mul_pred_add_self s (by omega)
  have hrc : 2 * Nat.choose r 2 + r = r * r := by omega
  have hsc : 2 * Nat.choose s 2 + s = s * s := by omega
  have hc3 : Nat.choose 3 2 = 3 := by decide
  have hcore : (3 * s - 4) + 4 = 3 * s := by omega
  simp only [strictM5, hc3]
  norm_num at ⊢
  rcases hregular with hd | hs5
  · have hd' : s + 2 ≤ r := by omega
    let e := r - s - 2
    have heq : e + 2 + s = r := by dsimp [e]; omega
    have he2 : 0 ≤ e * e := Nat.zero_le _
    nlinarith
  · have hd' : s + 1 ≤ r := by omega
    let d := r - s
    have heq : d + s = r := by dsimp [d]; omega
    have hd2 : 0 ≤ d * d := Nat.zero_le _
    nlinarith

theorem unbalancedTarget_le_m5_t4_simplex (r s : ℕ)
    (hs : 5 ≤ s) (hst : s < r) :
    quarterSquareCeil (r + s + 4 + 1) ≤ strictM5 r s 4 + simplexCard s 4 := by
  apply quarterSquareCeil_le_of_lt
  have hr := two_mul_choose_two_strict r
  have hs' := two_mul_choose_two_strict s
  have hrp := pred_add_one_eq (by omega : 1 ≤ r)
  have hsp := pred_add_one_eq (by omega : 1 ≤ s)
  have hrr := mul_pred_add_self r (by omega)
  have hss := mul_pred_add_self s (by omega)
  have hrc : 2 * Nat.choose r 2 + r = r * r := by omega
  have hsc : 2 * Nat.choose s 2 + s = s * s := by omega
  have hsimp := six_mul_simplexCard s 4 (by omega)
  have hsimp' : simplexCard s 4 = 6 * s - 14 := by
    norm_num at hsimp
    omega
  have hd' : s + 1 ≤ r := by omega
  let d := r - s
  have heq : d + s = r := by dsimp [d]; omega
  have hd2 : 0 ≤ d * d := Nat.zero_le _
  have hc4 : Nat.choose 4 2 = 6 := by decide
  have hspx : (6 * s - 14) + 14 = 6 * s := by omega
  simp only [strictM5, hc4]
  norm_num at ⊢
  nlinarith only [hrc, hsc, hsimp', hspx, heq, hd2, hs]

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

private theorem unbalancedTarget_le_m5_large_aux (r s t : ℕ)
    (ht : 5 ≤ t) (hts : t ≤ s) (hsr : s < r) :
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

theorem unbalancedTarget_le_m5_simplex_large (r s t : ℕ)
    (ht : 5 ≤ t) (hts : t ≤ s) (hsr : s < r) :
    quarterSquareCeil (r + s + t + 1) ≤ strictM5 r s t + simplexCard s t := by
  exact (unbalancedTarget_le_m5_large_aux r s t ht hts hsr).trans
    (Nat.add_le_add_left (simplexCard_large_lower s t ht hts) _)

theorem unbalancedTarget_le_m5_544 :
    quarterSquareCeil (5 + 4 + 4 + 1) ≤ strictM5 5 4 4 + 13 := by decide

theorem unbalancedTarget_le_m5_44_large (r : ℕ) (hr : 6 ≤ r) :
    quarterSquareCeil (r + 4 + 4 + 1) ≤ strictM5 r 4 4 + 14 := by
  apply quarterSquareCeil_le_of_lt
  have hc := two_mul_choose_two_strict r
  have hrp := pred_add_one_eq (by omega : 1 ≤ r)
  have hrr := mul_pred_add_self r (by omega)
  have hrc : 2 * Nat.choose r 2 + r = r * r := by omega
  let d := r - 6
  have heq : d + 6 = r := by dsimp [d]; omega
  have hd2 : 0 ≤ d * d := Nat.zero_le _
  have hc4 : Nat.choose 4 2 = 6 := by decide
  simp only [strictM5, hc4]
  norm_num at ⊢
  rw [← heq] at hc hrr hrc ⊢
  nlinarith

theorem unbalanced_residual_succ_s_2 (s : ℕ) (hs : 2 ≤ s) :
    quarterSquareCeil ((s + 1) + s + 2 + 1) = strictM5 (s + 1) s 2 + s := by
  have harg : (s + 1) + s + 2 + 1 = 2 * (s + 2) := by omega
  rw [harg, quarterSquareCeil_even]
  have hr := two_mul_choose_two_strict (s + 1)
  have hs' := two_mul_choose_two_strict s
  have hsp := pred_add_one_eq (by omega : 1 ≤ s)
  have hss := mul_pred_add_self s (by omega)
  have hrr := mul_pred_add_self (s + 1) (by omega)
  have hsc : 2 * Nat.choose s 2 + s = s * s := by omega
  have hrc : 2 * Nat.choose (s + 1) 2 + (s + 1) = (s + 1) * (s + 1) := by omega
  have hrs : s + 1 - 1 = s := by omega
  rw [hrs] at hr
  have hc2 : Nat.choose 2 2 = 1 := by decide
  simp only [strictM5, hc2]
  norm_num at ⊢
  nlinarith

theorem unbalanced_residual_433 :
    quarterSquareCeil (4 + 3 + 3 + 1) = strictM5 4 3 3 + 7 := by decide

theorem unbalanced_residual_543 :
    quarterSquareCeil (5 + 4 + 3 + 1) = strictM5 5 4 3 + 9 := by decide

end NSP3
