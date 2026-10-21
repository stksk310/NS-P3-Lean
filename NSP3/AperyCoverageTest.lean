import NSP3.AperyCoverage

namespace NSP3

-- Break caught: assuming an individual weight is a unit or restricting m to prime.
example (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    Function.Surjective (residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m)) :=
  apery_residue_surjective m a b c hm hgcd

end NSP3
