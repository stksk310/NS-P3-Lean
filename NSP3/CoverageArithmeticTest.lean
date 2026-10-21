import NSP3.CoverageArithmetic

example (S : AddSubmonoid ℕ) (m a b c : ℕ)
    (hm : m ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    NSP3.generatedAddSubmonoid m a b c ≤ S :=
  NSP3.Coverage.generated_le S m a b c hm ha hb hc

example (m a b c C : ℕ)
    (ht : ∀ n, C ≤ n → n ∈ NSP3.generatedSemigroup m a b c) :
    Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1 :=
  NSP3.Coverage.gcd_eq_one_of_tail m a b c C ht

-- A common factor 2 forbids a cofinite tail; gcd1 is proved, not presumed.
example : ¬ ∃ C, ∀ n, C ≤ n → n ∈ NSP3.generatedSemigroup 8 10 12 14 := by
  rintro ⟨C,ht⟩
  have h := NSP3.Coverage.gcd_eq_one_of_tail 8 10 12 14 C ht
  norm_num at h

-- Coefficient representations do not impose an order on the last three inputs.
example (S : AddSubmonoid ℕ) (hm : 4 ∈ S) (ha : 7 ∈ S)
    (hb : 5 ∈ S) (hc : 6 ∈ S) : NSP3.generatedAddSubmonoid 4 7 5 6 ≤ S :=
  NSP3.Coverage.generated_le S 4 7 5 6 hm ha hb hc
