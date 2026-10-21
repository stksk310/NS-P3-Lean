import NSP3.SymbolicFerrersArea

namespace NSP3
open Ferrers

-- Dropping the origin/axes or losing a strip breaks this exact cardinal contract.
example (S : CyclicStaircase) :
    (pair12PlaneSection S.D).card =
      (Finset.range (pair12Count S.D+1)).sum
        (fun i => (cornerX S (i+1)-cornerX S i)*cornerY S i) :=
  pair12_full_plane_card S

example (S : CyclicStaircase) :
    (plane12PosFinset S).card+pure1Intercept S+pure2Intercept S =
      (pair12PlaneSection S.D).card+1 := pair12_remove_axes S

example (S : CyclicStaircase) (k : ℕ) (hk : k ≤ pair12Count S.D+1) :
    (Finset.range k).sum (gapU S)+k = cornerX S k := gapU_prefix S hk

end NSP3
