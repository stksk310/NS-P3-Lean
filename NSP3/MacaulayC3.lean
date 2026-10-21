import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import NSP3.Macaulay

/-! The source Macaulay bound specialized to `e = 3` (embedding dimension four).
The degree is selected from the actual binomial interval, independently of P3.
The final strict bound is a polynomial argument for every degree at least four. -/
namespace NSP3
lemma c3_choose_two_poly (r : ℕ) : 2 * (r+2).choose 2 = (r+2)*(r+1) := by
  have h := Nat.choose_succ_right_eq (r+2) 1
  simp only [Nat.choose_one_right] at h
  have hs : r+2-1=r+1 := by omega
  rw [hs] at h
  nlinarith
lemma c3_choose_three_poly (r : ℕ) : 6 * (r+3).choose 3 = (r+3)*(r+2)*(r+1) := by
  have h := Nat.choose_succ_right_eq (r+3) 2
  have h2 := c3_choose_two_poly (r+1)
  have hs : r+3-2=r+1 := by omega
  rw [hs] at h
  nlinarith
lemma degree_le_choose (r : ℕ) : r ≤ (r+2).choose 3 := by
  induction r with
  | zero => omega
  | succ r ih =>
    have hp : 0 < (r+2).choose 2 := Nat.choose_pos (by omega)
    have he : (r+1+2).choose 3 = (r+2).choose 2 + (r+2).choose 3 := by
      simpa [Nat.add_assoc] using Nat.choose_succ_succ (r+2) 2
    omega
def c3Degree (m : ℕ) : ℕ := Nat.findGreatest (fun r => (r+2).choose 3 ≤ m) (m+1)
lemma c3Degree_pos (m : ℕ) (hm : 1 ≤ m) : 0 < c3Degree m := by
  have h : 1 ≤ c3Degree m := Nat.le_findGreatest (by omega) (by simpa using hm)
  omega
lemma c3Degree_interval (m : ℕ) (hm : 1 ≤ m) :
    (c3Degree m+2).choose 3 ≤ m ∧ m < (c3Degree m+3).choose 3 := by
  have hl : (c3Degree m+2).choose 3 ≤ m :=
    Nat.findGreatest_spec (P := fun r => (r+2).choose 3 ≤ m) (show 0 ≤ m+1 by omega)
      (by simpa only [Nat.zero_add, show Nat.choose 2 3 = 0 from by decide] using Nat.zero_le m)
  have hd : c3Degree m ≤ m := le_trans (degree_le_choose _) hl
  have hn := Nat.findGreatest_is_greatest (P := fun r => (r+2).choose 3 ≤ m)
    (show c3Degree m < c3Degree m+1 by omega) (show c3Degree m+1 ≤ m+1 by omega)
  constructor
  · exact hl
  · simpa [Nat.add_assoc] using Nat.lt_of_not_ge hn
lemma c3Degree_unique (m r : ℕ) (hm : 1 ≤ m)
    (hl : (r+2).choose 3 ≤ m) (hu : m < (r+3).choose 3) : c3Degree m = r := by
  obtain ⟨hdl,hdu⟩ := c3Degree_interval m hm
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have hmono := Nat.choose_le_choose 3 (show c3Degree m+3 ≤ r+2 by omega)
    omega
  · have hmono := Nat.choose_le_choose 3 (show r+3 ≤ c3Degree m+2 by omega)
    omega
lemma c3Degree_ge_four (m : ℕ) (hm : 20 ≤ m) : 4 ≤ c3Degree m := by
  obtain ⟨_,hu⟩ := c3Degree_interval m (by omega)
  by_contra hn
  have hmono := Nat.choose_le_choose 3 (show c3Degree m+3 ≤ 6 by omega)
  rw [show (6:ℕ).choose 3 = 20 from by decide] at hmono
  omega

lemma c3Degree_exists_unique (m : ℕ) (hm : 1 ≤ m) :
    ∃! r : ℕ, (r + 2).choose 3 ≤ m ∧ m < (r + 3).choose 3 := by
  refine ⟨c3Degree m, c3Degree_interval m hm, ?_⟩
  intro r h
  exact (c3Degree_unique m r hm h.1 h.2).symm

/-- The source remainder `s`, with subtraction justified by `c3Degree_interval`. -/
def c3Remainder (m : ℕ) : ℕ := m - (c3Degree m + 2).choose 3

/-- The exact source expression `choose(r+2,2) + s^{⟨r⟩} - s`. -/
def C3 (m : ℕ) : ℕ :=
  (c3Degree m + 2).choose 2 + macaulayRaise (c3Degree m) (c3Remainder m) -
    c3Remainder m

lemma c3Remainder_add_base (m : ℕ) (hm : 1 ≤ m) :
    c3Remainder m + (c3Degree m + 2).choose 3 = m :=
  Nat.sub_add_cancel (c3Degree_interval m hm).1

lemma c3Remainder_lt_binomial (m : ℕ) (hm : 1 ≤ m) :
    c3Remainder m < (c3Degree m + 2).choose 2 := by
  have he := c3Remainder_add_base m hm
  have hu := (c3Degree_interval m hm).2
  have hp : (c3Degree m + 3).choose 3 =
      (c3Degree m + 2).choose 2 + (c3Degree m + 2).choose 3 := by
    simpa [Nat.add_assoc] using Nat.choose_succ_succ (c3Degree m + 2) 2
  omega

/-- Raising cannot cause truncation in the final natural subtraction. -/
lemma C3_no_underflow (m : ℕ) (hm : 1 ≤ m) :
    c3Remainder m ≤ macaulayRaise (c3Degree m) (c3Remainder m) :=
  macaulayRaise_ge _ _ (c3Degree_pos m hm)

lemma C3_source_formula (m r : ℕ) (hm : 1 ≤ m)
    (hl : (r + 2).choose 3 ≤ m) (hu : m < (r + 3).choose 3) :
    C3 m = (r + 2).choose 2 + macaulayRaise r (m - (r + 2).choose 3) -
      (m - (r + 2).choose 3) := by
  simp only [C3, c3Remainder, c3Degree_unique m r hm hl hu]

lemma C3_ge_binomial (m : ℕ) (hm : 1 ≤ m) :
    (c3Degree m + 2).choose 2 ≤ C3 m := by
  have h := C3_no_underflow m hm
  unfold C3
  omega

/-- The unspecialized lower endpoint agrees with its `e=3` binomial form. -/
lemma c3_source_lower_binomial (r : ℕ) (hr : 1 ≤ r) :
    (r + 2).choose (r - 1) = (r + 2).choose 3 := by
  have he : r + 2 - 3 = r - 1 := by omega
  rw [← he]
  exact Nat.choose_symm (by omega)

lemma c3_source_upper_binomial (r : ℕ) :
    (r + 3).choose r = (r + 3).choose 3 := by
  exact Nat.choose_symm_of_eq_add (by omega)

lemma c3_source_base_binomial (r : ℕ) :
    (r + 2).choose r = (r + 2).choose 2 := by
  exact Nat.choose_symm_of_eq_add (by omega)

lemma C3_original_source_formula (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r)
    (hl : (r + 2).choose (r - 1) ≤ m) (hu : m < (r + 3).choose r) :
    C3 m = (r + 2).choose r +
      macaulayRaise r (m - (r + 2).choose (r - 1)) -
      (m - (r + 2).choose (r - 1)) := by
  rw [c3_source_lower_binomial r hr] at hl ⊢
  rw [c3_source_upper_binomial r] at hu
  rw [c3_source_base_binomial r]
  exact C3_source_formula m r hm hl hu

lemma c3_binomial_gap_identity (t : ℕ) :
    12 * (((t + 4 + 2).choose 2 - 2)^2) =
      48 * (t + 4 + 3).choose 3 +
        (3*t^4 + 58*t^3 + 375*t^2 + 860*t + 348) := by
  have hb := c3_choose_two_poly (t+4)
  have ht := c3_choose_three_poly (t+4)
  have hb2 : 2 ≤ (t+4+2).choose 2 := by
    have h := Nat.choose_le_choose 2 (show 4 ≤ t+4+2 by omega)
    rw [show (4:ℕ).choose 2 = 6 from by decide] at h
    omega
  have he := Nat.sub_add_cancel hb2
  nlinarith only [hb, ht, he]
lemma sqrt_bound_lt_binomial (r m : ℕ) (hr : 4 ≤ r) (hm : m < (r+3).choose 3) :
    2 + Nat.sqrt (4*m) < (r+2).choose 2 := by
  let B := (r+2).choose 2
  let T := (r+3).choose 3
  have hb2 : 2 ≤ B := by
    have h := Nat.choose_le_choose 2 (show 4 ≤ r+2 by omega)
    rw [show (4:ℕ).choose 2 = 6 from by decide] at h
    exact le_trans (by decide : 2 ≤ 6) h
  have he : B-2+2=B := Nat.sub_add_cancel hb2
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hr
  have hid : 12 * ((B-2)^2 : ℕ) = 48*T +
      (3*t^4+58*t^3+375*t^2+860*t+348) := by
    simpa [B, T, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      c3_binomial_gap_identity t
  have hs : 4*m < (B-2)^2 := by nlinarith
  have hroot : Nat.sqrt (4*m) < B-2 := Nat.sqrt_lt'.mpr hs
  omega
end NSP3
