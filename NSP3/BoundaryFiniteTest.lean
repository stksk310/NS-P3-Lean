import NSP3.BoundaryFinite

namespace NSP3

-- Break caught: finite boundary cover or exact membership theorem missing/weakened.
example (S : CyclicStaircase) : Finite {b : Point3 // MinimalComplement S.D b} :=
  minimalComplement_finite S

example (S : CyclicStaircase) (b : Point3) :
    b ∈ minimalComplementBoundaries S ↔ MinimalComplement S.D b :=
  mem_minimalComplementBoundaries S b

example (S : CyclicStaircase) :
    Nat.card {b : Point3 // MinimalComplement S.D b} =
      (minimalComplementBoundaries S).card := minimalComplement_card_eq_finset_card S

end NSP3
