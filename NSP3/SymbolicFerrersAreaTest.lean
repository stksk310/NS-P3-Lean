import NSP3.SymbolicFerrersArea

namespace NSP3

-- This typed contract fails if actual strip membership is absent or weakened.
example (S : CyclicStaircase) (i x y : ℕ) (hi : i ≤ pair12Count S.D)
    (hx : Ferrers.cornerX S i ≤ x) (hx' : x < Ferrers.cornerX S (i+1)) :
    Point3.mk x y 0 ∈ S.D ↔ y < Ferrers.cornerY S i :=
  Ferrers.pair12_strip_mem_iff S hi hx hx'

end NSP3
