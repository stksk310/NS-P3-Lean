import NSP3.BoundarySharp

namespace NSP3
attribute [local instance] Classical.propDecidable

-- Break caught: omission/double counting of a support class or wrong full indicator.
example (S : CyclicStaircase) :
    Nat.card {b : Point3 // MinimalComplement S.D b} =
      3 + pair12Count S.D + pair13Count S.D + pair23Count S.D +
        (if ∃ g, MinimalComplement S.D g ∧ FullSupport g then 1 else 0) :=
  boundary_card_exact S

-- Break caught: erroneous floor division or an extra hypothesis on the final bridge.
example (u m : ℕ) (h : quarterSquareCeil u ≤ m) : u ≤ Nat.sqrt (4*m) :=
  quarterSquareCeil_le_sqrt h

example (S : CyclicStaircase) :
    Nat.card {b : Point3 // MinimalComplement S.D b} ≤ 2 + Nat.sqrt (4*S.m) :=
  cyclicStaircase_boundary_card_sharp S

example (S : CyclicStaircase) (k : SupportKind) :
    (boundarySupport S k).card = supportBoundaryCard S k := boundary_support_card S k

example (S : CyclicStaircase) :
    (minimalComplementBoundaries S).card =
      ∑ k ∈ allSupportKinds, (boundarySupport S k).card := boundary_support_partition S

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    Nat.card {b : Point3 // MinimalComplement S.D b} =
      pair12Count S.D + pair13Count S.D + pair23Count S.D + 4 :=
  boundary_card_of_full S hg hf

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S) :
    Nat.card {b : Point3 // MinimalComplement S.D b} =
      pair12Count S.D + pair13Count S.D + pair23Count S.D + 3 :=
  boundary_card_of_noFull S hnf

-- Hand-checked rounded-square edges: zero, odd, even and nonsquare.
example : 0 ≤ Nat.sqrt (4*0) := quarterSquareCeil_le_sqrt (by decide : quarterSquareCeil 0 ≤ 0)
example : 3 ≤ Nat.sqrt (4*3) := quarterSquareCeil_le_sqrt (by decide : quarterSquareCeil 3 ≤ 3)
example : 4 ≤ Nat.sqrt (4*4) := quarterSquareCeil_le_sqrt (by decide : quarterSquareCeil 4 ≤ 4)

end NSP3
