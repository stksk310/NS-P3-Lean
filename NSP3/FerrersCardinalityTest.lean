import NSP3.FerrersCardinality

namespace NSP3

example (q : ℕ) : (pairTriangleIndices q).card = Nat.choose q 2 :=
  card_pairTriangleIndices q

example {D : Finset Point3} (hD : IsDownset D) {a₁ a₂ : ℕ}
    (h₁ : MinimalComplement D ⟨a₁, 0, 0⟩) (hp₁ : Pure1 ⟨a₁, 0, 0⟩)
    (h₂ : MinimalComplement D ⟨0, a₂, 0⟩) (hp₂ : Pure2 ⟨0, a₂, 0⟩) :
    a₁ + a₂ - 1 + Nat.choose (pair12Count D) 2 ≤ (pair12PlaneSection D).card :=
  pair12Plane_card_lower hD h₁ hp₁ h₂ hp₂

example {D : Finset Point3} (hD : IsDownset D) {a₁ a₃ : ℕ}
    (h₁ : MinimalComplement D ⟨a₁, 0, 0⟩) (hp₁ : Pure1 ⟨a₁, 0, 0⟩)
    (h₃ : MinimalComplement D ⟨0, 0, a₃⟩) (hp₃ : Pure3 ⟨0, 0, a₃⟩) :
    a₁ + a₃ - 1 + Nat.choose (pair13Count D) 2 ≤ (pair13PlaneSection D).card :=
  pair13Plane_card_lower hD h₁ hp₁ h₃ hp₃

example {D : Finset Point3} (hD : IsDownset D) {a₂ a₃ : ℕ}
    (h₂ : MinimalComplement D ⟨0, a₂, 0⟩) (hp₂ : Pure2 ⟨0, a₂, 0⟩)
    (h₃ : MinimalComplement D ⟨0, 0, a₃⟩) (hp₃ : Pure3 ⟨0, 0, a₃⟩) :
    a₂ + a₃ - 1 + Nat.choose (pair23Count D) 2 ≤ (pair23PlaneSection D).card :=
  pair23Plane_card_lower hD h₂ hp₂ h₃ hp₃

end NSP3
