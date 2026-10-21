import NSP3.AperyConstruction

namespace NSP3

-- Break caught: moving coverage, tie/downclosure or minimum weight to an assumption.
example (m a b c : ℕ) (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    ∃ D : Finset Point3, IsDownset D ∧
      ∃ e : {q : Point3 // q ∈ D} ≃ ZMod m,
        (∀ q, e q = residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q.1) ∧
        ∀ q ∈ D, ∀ u : Point3,
          residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) u =
            residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q →
          a*q.x + b*q.y + c*q.z ≤ a*u.x + b*u.y + c*u.z :=
  apery_staircase_exists m a b c hm ha hb hc hgcd

end NSP3
