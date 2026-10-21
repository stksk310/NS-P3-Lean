import NSP3.Main

namespace NSP3
-- Catches a correct isolated result that the aggregate import does not expose.
example (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    minimumFourInputRelations m a b c ≤ 2 + Nat.sqrt (4*m) :=
  minimal_presentation_four_input_sharp m a b c hm hgcd
end NSP3
