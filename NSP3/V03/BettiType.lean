import NSP3.V03.BettiApery

namespace NSP3.V03

/-- The cardinality of the actual set of nonnegative pseudo-Frobenius gaps. -/
noncomputable def pseudoFrobeniusType (m a b c : ℕ) : ℕ :=
  ({f : ℕ | IsPseudoFrobenius m a b c f} : Set ℕ).ncard

theorem pseudoFrobeniusType_eq_finset_card (m a b c : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    pseudoFrobeniusType m a b c =
      (pseudoFrobeniusFinset m a b c hm hgcd).card := by
  classical
  have he : ({f : ℕ | IsPseudoFrobenius m a b c f} : Set ℕ) =
      (pseudoFrobeniusFinset m a b c hm hgcd : Set ℕ) := by
    ext f
    exact (mem_pseudoFrobeniusFinset m a b c f hm ha hb hc hgcd).symm
  unfold pseudoFrobeniusType
  rw [he,Set.ncard_coe_finset]

theorem pseudoFrobeniusType_le_maximalPoints (m a b c : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    pseudoFrobeniusType m a b c ≤
      (maximalPoints (aperyStandardSet m a b c hm hgcd)).card := by
  rw [pseudoFrobeniusType_eq_finset_card m a b c hm ha hb hc hgcd]
  exact pseudoFrobenius_card_le_maximalPoints m a b c hm hgcd

end NSP3.V03
