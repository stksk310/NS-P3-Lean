import NSP3.PresentationBoundary

namespace NSP3
-- Catches unsound numeric edges, omitted equal-weight lex ties, and hidden positivity assumptions.
example (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (p : Point3) (hp : MinimalComplement (aperyStandardSet m a b c hm hgcd) p) :
    ∃ h : ℕ, ∃ q ∈ aperyStandardSet m a b c hm hgcd,
      aperyWeight a b c p = aperyWeight a b c q + h*m ∧
      aperyKey a b c q < aperyKey a b c p :=
  presentation_border_replacement m a b c hm hgcd p hp

-- Catches an arbitrary equivalence closure that does not preserve the true factor map.
example (m a b c : ℕ) (R : Finset (Fact4 × Fact4))
    (hs : ∀ e ∈ R, factorWeight m a b c e.1 = factorWeight m a b c e.2)
    (u v : Fact4) (h : PresentationRel R u v) :
    factorWeight m a b c u = factorWeight m a b c v :=
  presentationRel_sound m a b c R hs h
end NSP3
