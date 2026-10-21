import NSP3.SymbolicTGE4Core

namespace NSP3

-- Break caught: exact row length must respect both pair cuts and yz cut.
example (S : CyclicStaircase) (y z : ℕ) (hy : 0 < y) (hz : 0 < z) :
    ((fullCoreFinset S).filter (fun p => p.y=y ∧ p.z=z)).card =
      if y+z ≤ pair23Count S.D then
        min (pair12Count S.D-y) (pair13Count S.D-z) else 0 :=
  fullCore_positive_row_card S y z hy hz

-- Break caught: the q444 core has eleven, not the ten-point simplex lower.
example (S : CyclicStaircase) (hr : 4 ≤ pair12Count S.D)
    (hs : 4 ≤ pair13Count S.D) (ht : 4 ≤ pair23Count S.D) :
    11 ≤ (fullCoreFinset S).card := fullCore_eleven_lower S hr hs ht

example (S : CyclicStaircase) (hr : pair12Count S.D=4)
    (hs : pair13Count S.D=4) (ht : pair23Count S.D=4) :
    (fullCoreFinset S).card=11 := fullCore_q444_card S hr hs ht

end NSP3
