import NSP3.PresentationNormalization

namespace NSP3
-- Catches replacing actual generation by an assumed normalization or a finite step cap.
example (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) (u v : Fact4) :
    PresentationRel (boundaryRelations m a b c hm hgcd) u v ↔
      factorWeight m a b c u = factorWeight m a b c v :=
  boundaryRelations_generate m a b c hm hgcd u v
end NSP3
