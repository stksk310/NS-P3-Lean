import NSP3.BoundaryDescent

namespace NSP3

example {D : Finset Point3} {x : Point3} (hx : x ∉ D) :
    ∃ b, MinimalComplement D b ∧ b ≤ x :=
  exists_minimalComplement_le hx

example : MinimalComplement (∅ : Finset Point3) Point3.zero := by
  simp [MinimalComplement, Point3.zero, Point3.pred1, Point3.pred2, Point3.pred3]

example : ∃ b, MinimalComplement (∅ : Finset Point3) b ∧ b ≤ Point3.zero := by
  exact exists_minimalComplement_le (by simp)

example {D : Finset Point3} (hD : IsDownset D) {b c : Point3}
    (hb : MinimalComplement D b) (hc : MinimalComplement D c) (hbc : b ≠ c) :
    ¬ b ≤ c :=
  minimalComplement_not_le_of_ne hD hb hc hbc

example {D : Finset Point3} (hD : IsDownset D) {b c : Point3}
    (hb : MinimalComplement D b) (hc : MinimalComplement D c) (hbc : b ≠ c) :
    (¬ b ≤ c) ∧ (¬ c ≤ b) :=
  minimalComplements_incomparable hD hb hc hbc

example {D : Finset Point3} (hD : IsDownset D) (hne : D.Nonempty) :
    ∃ a, MinimalComplement D ⟨a, 0, 0⟩ ∧ Pure1 ⟨a, 0, 0⟩ :=
  exists_pure1_minimalComplement hD hne

example {D : Finset Point3} (hD : IsDownset D) (hne : D.Nonempty) :
    ∃ a, MinimalComplement D ⟨0, a, 0⟩ ∧ Pure2 ⟨0, a, 0⟩ :=
  exists_pure2_minimalComplement hD hne

example {D : Finset Point3} (hD : IsDownset D) (hne : D.Nonempty) :
    ∃ a, MinimalComplement D ⟨0, 0, a⟩ ∧ Pure3 ⟨0, 0, a⟩ :=
  exists_pure3_minimalComplement hD hne

end NSP3
