import NSP3.PairReturns
import NSP3.PairFerrers

namespace NSP3

noncomputable def pair12BoundaryEquiv (S : CyclicStaircase) :
    Pair12Boundary S ≃ {b : Point3 // b ∈ pair12Boundaries S.D} where
  toFun b := ⟨b.1, mem_pair12Boundaries.mpr b.2⟩
  invFun b := ⟨b.1, mem_pair12Boundaries.mp b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def pair13BoundaryEquiv (S : CyclicStaircase) :
    Pair13Boundary S ≃ {b : Point3 // b ∈ pair13Boundaries S.D} where
  toFun b := ⟨b.1, mem_pair13Boundaries.mpr b.2⟩
  invFun b := ⟨b.1, mem_pair13Boundaries.mp b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def pair23BoundaryEquiv (S : CyclicStaircase) :
    Pair23Boundary S ≃ {b : Point3 // b ∈ pair23Boundaries S.D} where
  toFun b := ⟨b.1, mem_pair23Boundaries.mpr b.2⟩
  invFun b := ⟨b.1, mem_pair23Boundaries.mp b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance (S : CyclicStaircase) : Fintype (Pair12Boundary S) :=
  Fintype.ofEquiv {b : Point3 // b ∈ pair12Boundaries S.D}
    (pair12BoundaryEquiv S).symm

noncomputable instance (S : CyclicStaircase) : Fintype (Pair13Boundary S) :=
  Fintype.ofEquiv {b : Point3 // b ∈ pair13Boundaries S.D}
    (pair13BoundaryEquiv S).symm

noncomputable instance (S : CyclicStaircase) : Fintype (Pair23Boundary S) :=
  Fintype.ofEquiv {b : Point3 // b ∈ pair23Boundaries S.D}
    (pair23BoundaryEquiv S).symm

@[simp] theorem card_pair12Boundary (S : CyclicStaircase) :
    Fintype.card (Pair12Boundary S) = pair12Count S.D := by
  change Fintype.card (Pair12Boundary S) = (pair12Boundaries S.D).card
  calc
    Fintype.card (Pair12Boundary S) =
        Fintype.card {b : Point3 // b ∈ pair12Boundaries S.D} :=
      Fintype.card_congr (pair12BoundaryEquiv S)
    _ = (pair12Boundaries S.D).card := Fintype.card_coe _

@[simp] theorem card_pair13Boundary (S : CyclicStaircase) :
    Fintype.card (Pair13Boundary S) = pair13Count S.D := by
  change Fintype.card (Pair13Boundary S) = (pair13Boundaries S.D).card
  calc
    Fintype.card (Pair13Boundary S) =
        Fintype.card {b : Point3 // b ∈ pair13Boundaries S.D} :=
      Fintype.card_congr (pair13BoundaryEquiv S)
    _ = (pair13Boundaries S.D).card := Fintype.card_coe _

@[simp] theorem card_pair23Boundary (S : CyclicStaircase) :
    Fintype.card (Pair23Boundary S) = pair23Count S.D := by
  change Fintype.card (Pair23Boundary S) = (pair23Boundaries S.D).card
  calc
    Fintype.card (Pair23Boundary S) =
        Fintype.card {b : Point3 // b ∈ pair23Boundaries S.D} :=
      Fintype.card_congr (pair23BoundaryEquiv S)
    _ = (pair23Boundaries S.D).card := Fintype.card_coe _

end NSP3
