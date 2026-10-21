import NSP3.Main

namespace NSP3

example (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    ∃ D : Finset Point3, IsDownset D ∧ D.card = m := by
  exact ⟨aperyStandardSet m a b c hm hgcd,
    aperyStandardSet_downset m a b c hm hgcd, aperyStandardSet_card m a b c hm hgcd⟩

end NSP3
