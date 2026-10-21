import NSP3.Main

namespace NSP3
-- Catches omission of the new numeric bridge from the aggregate API.
example (m a b c : ℕ) (hm : 0 < m)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    {n : ℕ | (∃ k x y z : ℕ, n = k*m + a*x + b*y + c*z) ∧
      (n < m ∨ ¬ ∃ k x y z : ℕ, n-m = k*m + a*x + b*y + c*z)} =
    {n : ℕ | ∃ q ∈ aperyStandardSet m a b c hm hgcd, n = aperyWeight a b c q} :=
  generated_semigroup_apery_weight_set m a b c hm ha hb hc hgcd
end NSP3
