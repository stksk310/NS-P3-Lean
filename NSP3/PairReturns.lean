import NSP3.ReturnGeometry

namespace NSP3

open CyclicStaircase

theorem pair12_return_eq_axis3 (S : CyclicStaircase) {b : Point3}
    (hb : MinimalComplement S.D b) (hp : Pair12 b) :
    ∃ c : ℕ, S.rho b = ⟨0, 0, c⟩ := by
  refine ⟨(S.rho b).z, ?_⟩
  apply Point3.ext
  · exact complementFaceReturn₁ S hb hp.1
  · exact complementFaceReturn₂ S hb hp.2.1
  · rfl

theorem pair13_return_eq_axis2 (S : CyclicStaircase) {b : Point3}
    (hb : MinimalComplement S.D b) (hp : Pair13 b) :
    ∃ c : ℕ, S.rho b = ⟨0, c, 0⟩ := by
  refine ⟨(S.rho b).y, ?_⟩
  apply Point3.ext
  · exact complementFaceReturn₁ S hb hp.1
  · rfl
  · exact complementFaceReturn₃ S hb hp.2.2

theorem pair23_return_eq_axis1 (S : CyclicStaircase) {b : Point3}
    (hb : MinimalComplement S.D b) (hp : Pair23 b) :
    ∃ c : ℕ, S.rho b = ⟨c, 0, 0⟩ := by
  refine ⟨(S.rho b).x, ?_⟩
  apply Point3.ext
  · rfl
  · exact complementFaceReturn₂ S hb hp.2.1
  · exact complementFaceReturn₃ S hb hp.2.2

def Pair12Boundary (S : CyclicStaircase) :=
  {b : Point3 // MinimalComplement S.D b ∧ Pair12 b}

def Pair13Boundary (S : CyclicStaircase) :=
  {b : Point3 // MinimalComplement S.D b ∧ Pair13 b}

def Pair23Boundary (S : CyclicStaircase) :=
  {b : Point3 // MinimalComplement S.D b ∧ Pair23 b}

def pair12ReturnCoord (S : CyclicStaircase) (b : Pair12Boundary S) : ℕ :=
  (S.rho b.1).z

def pair13ReturnCoord (S : CyclicStaircase) (b : Pair13Boundary S) : ℕ :=
  (S.rho b.1).y

def pair23ReturnCoord (S : CyclicStaircase) (b : Pair23Boundary S) : ℕ :=
  (S.rho b.1).x

theorem pair12ReturnCoord_injective (S : CyclicStaircase) :
    Function.Injective (pair12ReturnCoord S) := by
  intro b c hcoord
  apply Subtype.ext
  by_contra hbc
  have hrne : S.rho b.1 ≠ S.rho c.1 :=
    return_ne_of_support_inter S b.2.1 c.2.1 hbc
      (Or.inl ⟨b.2.2.1, c.2.2.1⟩)
  apply hrne
  apply Point3.ext
  · rw [complementFaceReturn₁ S b.2.1 b.2.2.1,
      complementFaceReturn₁ S c.2.1 c.2.2.1]
  · rw [complementFaceReturn₂ S b.2.1 b.2.2.2.1,
      complementFaceReturn₂ S c.2.1 c.2.2.2.1]
  · exact hcoord

theorem pair13ReturnCoord_injective (S : CyclicStaircase) :
    Function.Injective (pair13ReturnCoord S) := by
  intro b c hcoord
  apply Subtype.ext
  by_contra hbc
  have hrne : S.rho b.1 ≠ S.rho c.1 :=
    return_ne_of_support_inter S b.2.1 c.2.1 hbc
      (Or.inl ⟨b.2.2.1, c.2.2.1⟩)
  apply hrne
  apply Point3.ext
  · rw [complementFaceReturn₁ S b.2.1 b.2.2.1,
      complementFaceReturn₁ S c.2.1 c.2.2.1]
  · exact hcoord
  · rw [complementFaceReturn₃ S b.2.1 b.2.2.2.2,
      complementFaceReturn₃ S c.2.1 c.2.2.2.2]

theorem pair23ReturnCoord_injective (S : CyclicStaircase) :
    Function.Injective (pair23ReturnCoord S) := by
  intro b c hcoord
  apply Subtype.ext
  by_contra hbc
  have hrne : S.rho b.1 ≠ S.rho c.1 :=
    return_ne_of_support_inter S b.2.1 c.2.1 hbc
      (Or.inr (Or.inl ⟨b.2.2.2.1, c.2.2.2.1⟩))
  apply hrne
  apply Point3.ext
  · exact hcoord
  · rw [complementFaceReturn₂ S b.2.1 b.2.2.2.1,
      complementFaceReturn₂ S c.2.1 c.2.2.2.1]
  · rw [complementFaceReturn₃ S b.2.1 b.2.2.2.2,
      complementFaceReturn₃ S c.2.1 c.2.2.2.2]

end NSP3
