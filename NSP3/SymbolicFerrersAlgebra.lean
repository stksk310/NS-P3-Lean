import NSP3.SymbolicFerrersRank

namespace NSP3.Ferrers
open Finset

def upperSum (n : ℕ) (f : ℕ → ℕ → ℕ) : ℕ :=
  ∑ i ∈ range n, ∑ j ∈ range n, if i ≤ j then f i j else 0

theorem range_filter_ge (n i : ℕ) :
    (range n).filter (fun j => i ≤ j) = Ico i n := by ext j; simp; omega

theorem range_filter_le {n j : ℕ} (hj : j<n) :
    (range n).filter (fun i => i ≤ j) = range (j+1) := by ext i; simp; omega

theorem upperSum_left (n : ℕ) (u : ℕ → ℕ) :
    upperSum n (fun i _ => u i) = ∑ i ∈ range n, (n-i)*u i := by
  unfold upperSum
  apply sum_congr rfl
  intro i _
  rw [← sum_filter,range_filter_ge]
  simp

theorem upperSum_right (n : ℕ) (v : ℕ → ℕ) :
    upperSum n (fun _ j => v j) = ∑ j ∈ range n, (j+1)*v j := by
  unfold upperSum
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [← sum_filter,range_filter_le (mem_range.mp hj)]
  simp

theorem sum_range_id_choose (n : ℕ) : (∑ i ∈ range n, i)=Nat.choose n 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ,ih,Nat.choose_succ_succ]
    simp [Nat.add_comm]

theorem upperSum_one (n : ℕ) : upperSum n (fun _ _ => 1)=Nat.choose n 2+n := by
  rw [upperSum_right]
  simp [sum_add_distrib,sum_range_id_choose]

theorem upperSum_add (n : ℕ) (f g : ℕ → ℕ → ℕ) :
    upperSum n (fun i j => f i j+g i j)=upperSum n f+upperSum n g := by
  have he (i j : ℕ) : (if i ≤ j then f i j+g i j else 0) =
      (if i ≤ j then f i j else 0)+(if i ≤ j then g i j else 0) := by
    split <;> simp_all
  simp only [upperSum,he,sum_add_distrib]

/-- Pure finite-sum algebra; no geometric premise is hidden in this identity. -/
theorem upperSum_expand (n : ℕ) (u v : ℕ → ℕ) :
    upperSum n (fun i j => (1+u i)*(1+v j)) =
      Nat.choose n 2+n+
      (range n).sum (fun i => (n-i)*u i)+
      (range n).sum (fun j => (j+1)*v j)+upperSum n (fun i j => u i*v j) := by
  have he : (fun i j => (1+u i)*(1+v j)) =
      (fun i j => 1+u i+v j+u i*v j) := by funext i j; ring
  rw [he,upperSum_add,upperSum_add,upperSum_add,upperSum_one,
    upperSum_left,upperSum_right]

end NSP3.Ferrers
