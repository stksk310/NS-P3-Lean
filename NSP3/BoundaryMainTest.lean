import NSP3.Main

namespace NSP3

-- Break caught: aggregate Main fails to expose the actual new boundary theorem.
example (S : CyclicStaircase) :
    Nat.card {b : Point3 // MinimalComplement S.D b} ≤ 2 + Nat.sqrt (4*S.m) :=
  cyclicStaircase_boundary_card_sharp S

end NSP3
