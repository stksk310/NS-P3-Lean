import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-!
Canonical Macaulay expansions. A list `[aᵣ, aᵣ₋₁, …, aⱼ]` stores the tops
of the binomial coefficients, starting at index `r`. Valid lists have positive
indices, `aᵢ ≥ i`, and strictly descending tops. The empty list represents zero.
The greedy construction is proved valid, reconstructs its input, and is the
unique valid expansion of that input; raising replaces each `choose aᵢ i`
by `choose (aᵢ + 1) (i + 1)`.
-/
namespace NSP3
lemma choose_offset_lower (n r : ℕ) (hr : 0 < r) : n + 1 ≤ (n + r).choose r := by
  induction r with
  | zero => omega
  | succ r ih =>
    cases r with
    | zero => simp
    | succ r =>
      have h := ih (by omega)
      rw [show n + (r + 1 + 1) = (n + (r + 1)) + 1 by omega, Nat.choose_succ_succ']
      omega

/-- Largest top whose index-`r` binomial coefficient does not exceed `n`.
The finite search bound is justified by `choose_offset_lower`. -/
def macaulayTop (r n : ℕ) : ℕ := Nat.findGreatest (fun a => a.choose r ≤ n) (n + r)
lemma macaulayTop_spec (r n : ℕ) (hr : 0 < r) (hn : 0 < n) :
    r ≤ macaulayTop r n ∧ (macaulayTop r n).choose r ≤ n ∧
    n < (macaulayTop r n + 1).choose r := by
  have hp : r.choose r ≤ n := by simpa using (show 1 ≤ n by omega)
  have hlo : r ≤ macaulayTop r n := Nat.le_findGreatest (P := fun a => a.choose r ≤ n) (by omega) hp
  have hs : (macaulayTop r n).choose r ≤ n := Nat.findGreatest_spec (P := fun a => a.choose r ≤ n) (show r ≤ n + r by omega) hp
  refine ⟨hlo, hs, ?_⟩
  by_cases hb : macaulayTop r n + 1 ≤ n + r
  · exact Nat.lt_of_not_ge (Nat.findGreatest_is_greatest (P := fun a => a.choose r ≤ n) (by change macaulayTop r n < macaulayTop r n + 1; omega) hb)
  · have hbound := Nat.findGreatest_le (P := fun a => a.choose r ≤ n) (n + r)
    have heq : macaulayTop r n = n + r := by change macaulayTop r n ≤ n + r at hbound; omega
    have hh := choose_offset_lower n r hr
    rw [heq] at hs
    omega

/-- Greedy binomial tops, omitting all zero summands. -/
def macaulayDigits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | r + 1, n => if n = 0 then [] else
      let a := macaulayTop (r + 1) n
      a :: macaulayDigits r (n - a.choose (r + 1))
/-- Sum of `choose aᵢ i` with indices decreasing from `r`. -/
def binomialValue : ℕ → List ℕ → ℕ
  | _, [] => 0
  | r, a :: ds => a.choose r + binomialValue (r - 1) ds
/-- Source Macaulay sum: replace each summand by `choose (aᵢ+1) (i+1)`. -/
def raisedBinomialValue : ℕ → List ℕ → ℕ
  | _, [] => 0
  | r, a :: ds => (a + 1).choose (r + 1) + raisedBinomialValue (r - 1) ds
/-- The Macaulay raising operator, using the unique valid binomial expansion. -/
def macaulayRaise (r n : ℕ) : ℕ := raisedBinomialValue r (macaulayDigits r n)
@[simp] theorem macaulayRaise_zero (r : ℕ) : macaulayRaise r 0 = 0 := by
  cases r <;> simp [macaulayRaise, macaulayDigits, raisedBinomialValue]
theorem macaulayDigits_reconstruct (r n : ℕ) (hr : 0 < r) :
    binomialValue r (macaulayDigits r n) = n := by
  induction r generalizing n with
  | zero => omega
  | succ r ih =>
    by_cases hn : n = 0
    · subst n; simp [macaulayDigits, binomialValue]
    · have hs := macaulayTop_spec (r + 1) n (by omega) (by omega)
      simp only [macaulayDigits, hn, ↓reduceIte, binomialValue, Nat.add_sub_cancel]
      cases r with
      | zero =>
        simp only [Nat.zero_add, Nat.choose_one_right, macaulayDigits, binomialValue, add_zero] at *
        omega
      | succ r => rw [ih _ (by omega)]; omega
lemma binomialValue_le_raised (r : ℕ) (ds : List ℕ) :
    binomialValue r ds ≤ raisedBinomialValue r ds := by
  induction ds generalizing r with
  | nil => simp [binomialValue, raisedBinomialValue]
  | cons a ds ih =>
    simp only [binomialValue, raisedBinomialValue, Nat.choose_succ_succ']
    have h := ih (r - 1)
    omega
theorem macaulayRaise_ge (r n : ℕ) (hr : 0 < r) : n ≤ macaulayRaise r n := by
  have h := binomialValue_le_raised r (macaulayDigits r n)
  simpa only [macaulayRaise, macaulayDigits_reconstruct r n hr] using h
end NSP3
namespace NSP3
/-- Exact expansion conditions: positive indices, top at least index, and
strictly descending tops. Empty lists allow the standard zero convention. -/
def MacaulayValid : ℕ → List ℕ → Prop
  | _, [] => True
  | 0, _ :: _ => False
  | r + 1, a :: ds => r + 1 ≤ a ∧ MacaulayValid r ds ∧ ∀ b ∈ ds, b < a
lemma valid_value_bound (r A : ℕ) (ds : List ℕ) (hv : MacaulayValid r ds)
    (hd : ∀ b ∈ ds, b < A) (hA : r ≤ A) : binomialValue r ds < A.choose r := by
  induction ds generalizing r A with
  | nil => simpa [binomialValue] using Nat.choose_pos hA
  | cons a ds ih =>
    cases r with
    | zero => simp [MacaulayValid] at hv
    | succ r =>
      obtain ⟨ha, hv, hh⟩ := hv
      have ht := ih r a hv hh (by omega)
      have he : a < A := hd a (by simp)
      have hc := Nat.choose_le_choose (r + 1) (show a + 1 ≤ A by omega)
      simp only [binomialValue, Nat.add_sub_cancel]
      rw [Nat.choose_succ_succ'] at hc
      omega
lemma macaulay_residual_lt (r n : ℕ) (hn : 0 < n) :
    n - (macaulayTop (r + 1) n).choose (r + 1) <
      (macaulayTop (r + 1) n).choose r := by
  have hs := macaulayTop_spec (r + 1) n (by omega) hn
  rw [Nat.choose_succ_succ'] at hs
  omega
lemma valid_all_lt_of_value_lt (r A : ℕ) (ds : List ℕ)
    (hv : MacaulayValid r ds) (hn : binomialValue r ds < A.choose r) :
    ∀ b ∈ ds, b < A := by
  cases ds with
  | nil => simp
  | cons a ds =>
    cases r with
    | zero => simp [MacaulayValid] at hv
    | succ r =>
      obtain ⟨ha, hv, hd⟩ := hv
      have ht : a < A := by
        by_contra hh
        have hc := Nat.choose_le_choose (r + 1) (show A ≤ a by omega)
        simp only [binomialValue] at hn
        omega
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact ht
      · exact lt_trans (hd b hb) ht
theorem macaulayDigits_valid (r n : ℕ) : MacaulayValid r (macaulayDigits r n) := by
  induction r generalizing n with
  | zero => simp [macaulayDigits, MacaulayValid]
  | succ r ih =>
    by_cases hn : n = 0
    · subst n; simp [macaulayDigits, MacaulayValid]
    · have hs := macaulayTop_spec (r + 1) n (by omega) (by omega)
      simp only [macaulayDigits, hn, ↓reduceIte, MacaulayValid]
      refine ⟨hs.1, ih _, ?_⟩
      apply valid_all_lt_of_value_lt r _ _ (ih _)
      cases r with
      | zero =>
        simp only [macaulayDigits, binomialValue]
        have hp := Nat.choose_pos (show 0 ≤ macaulayTop 1 n by omega)
        exact hp
      | succ r =>
        rw [macaulayDigits_reconstruct _ _ (by omega)]
        exact macaulay_residual_lt _ _ (by omega)
end NSP3

namespace NSP3
lemma valid_value_pos (r a : ℕ) (ds : List ℕ) (hv : MacaulayValid r (a :: ds)) :
    0 < binomialValue r (a :: ds) := by
  cases r with
  | zero => simp [MacaulayValid] at hv
  | succ r =>
    have hp := Nat.choose_pos hv.1
    simp only [binomialValue]
    omega
lemma valid_head_interval (r a : ℕ) (ds : List ℕ) (hv : MacaulayValid (r + 1) (a :: ds)) :
    a.choose (r + 1) ≤ binomialValue (r + 1) (a :: ds) ∧
    binomialValue (r + 1) (a :: ds) < (a + 1).choose (r + 1) := by
  have hb := valid_value_bound r a ds hv.2.1 hv.2.2 (by have := hv.1; omega)
  simp only [binomialValue, Nat.add_sub_cancel, Nat.choose_succ_succ']
  omega
lemma valid_head_eq_greedy (r a : ℕ) (ds : List ℕ)
    (hv : MacaulayValid (r + 1) (a :: ds)) :
    a = macaulayTop (r + 1) (binomialValue (r + 1) (a :: ds)) := by
  have hi := valid_head_interval r a ds hv
  have hg := macaulayTop_spec (r + 1) _ (by omega) (valid_value_pos _ _ _ hv)
  apply Nat.le_antisymm
  · by_contra hh
    have hc := Nat.choose_le_choose (r + 1)
      (show macaulayTop (r + 1) (binomialValue (r + 1) (a :: ds)) + 1 ≤ a by omega)
    omega
  · by_contra hh
    have hc := Nat.choose_le_choose (r + 1)
      (show a + 1 ≤ macaulayTop (r + 1) (binomialValue (r + 1) (a :: ds)) by omega)
    omega
theorem macaulayDigits_unique (r : ℕ) (ds : List ℕ) (hv : MacaulayValid r ds) :
    ds = macaulayDigits r (binomialValue r ds) := by
  induction r generalizing ds with
  | zero =>
    cases ds with
    | nil => rfl
    | cons a ds => simp [MacaulayValid] at hv
  | succ r ih =>
    cases ds with
    | nil => simp [binomialValue, macaulayDigits]
    | cons a ds =>
      have hp := valid_value_pos (r + 1) a ds hv
      have he := valid_head_eq_greedy r a ds hv
      simp only [macaulayDigits, ne_of_gt hp, ↓reduceIte, ← he]
      congr 1
      simp only [binomialValue, Nat.add_sub_cancel, Nat.add_sub_cancel_left]
      exact ih ds hv.2.1
theorem macaulayExpansion_unique (r n : ℕ) (ds : List ℕ)
    (hv : MacaulayValid r ds) (hn : binomialValue r ds = n) :
    ds = macaulayDigits r n := by
  rw [← hn]
  exact macaulayDigits_unique r ds hv
theorem macaulayRaise_source (r n : ℕ) :
    macaulayRaise r n = raisedBinomialValue r (macaulayDigits r n) := rfl
end NSP3




namespace NSP3
/-- A valid expansion never reaches index zero with a nonzero summand. -/
theorem macaulayValid_length_le (r : ℕ) (ds : List ℕ) (hv : MacaulayValid r ds) :
    ds.length ≤ r := by
  induction ds generalizing r with
  | nil => simp
  | cons a ds ih =>
    cases r with
    | zero => simp [MacaulayValid] at hv
    | succ r =>
      exact Nat.succ_le_succ (ih r hv.2.1)
/-- Every pair of tops in the canonical expansion is strictly descending. -/
theorem macaulayDigits_descending (r n : ℕ) :
    (macaulayDigits r n).Pairwise (fun a b => b < a) := by
  have hv := macaulayDigits_valid r n
  generalize macaulayDigits r n = ds at *
  induction ds generalizing r with
  | nil => exact List.Pairwise.nil
  | cons a ds ih =>
    cases r with
    | zero => simp [MacaulayValid] at hv
    | succ r =>
      exact List.pairwise_cons.mpr ⟨hv.2.2, ih r hv.2.1⟩
/-- Raising computed from any valid r-binomial expansion agrees with the canonical operator. -/
theorem macaulayRaise_of_expansion (r n : ℕ) (ds : List ℕ)
    (hv : MacaulayValid r ds) (hn : binomialValue r ds = n) :
    macaulayRaise r n = raisedBinomialValue r ds := by
  rw [macaulayExpansion_unique r n ds hv hn]
  rfl
end NSP3
