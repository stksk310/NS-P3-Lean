import NSP3.PairFerrers

namespace NSP3

example {D : Finset Point3} {b : Point3} :
    b ∈ pair12Boundaries D ↔ MinimalComplement D b ∧ Pair12 b :=
  mem_pair12Boundaries

example {D : Finset Point3} {b : Point3} :
    b ∈ pair13Boundaries D ↔ MinimalComplement D b ∧ Pair13 b :=
  mem_pair13Boundaries

example {D : Finset Point3} {b : Point3} :
    b ∈ pair23Boundaries D ↔ MinimalComplement D b ∧ Pair23 b :=
  mem_pair23Boundaries

example (D : Finset Point3) : pair12Count D = (pair12Boundaries D).card := rfl
example (D : Finset Point3) : pair13Count D = (pair13Boundaries D).card := rfl
example (D : Finset Point3) : pair23Count D = (pair23Boundaries D).card := rfl

example : pair12Count (∅ : Finset Point3) = 0 := by
  simp [pair12Count, pair12Boundaries]

example : pair13Count (∅ : Finset Point3) = 0 := by
  simp [pair13Count, pair13Boundaries]

example : pair23Count (∅ : Finset Point3) = 0 := by
  simp [pair23Count, pair23Boundaries]

example {D : Finset Point3} (hD : IsDownset D) {b c : Point3}
    (hb : b ∈ pair12Boundaries D) (hc : c ∈ pair12Boundaries D)
    (hxy : b.x = c.x) : b = c :=
  pair12_eq_of_x_eq hD hb hc hxy

example {D : Finset Point3} (hD : IsDownset D) {b c : Point3}
    (hb : b ∈ pair12Boundaries D) (hc : c ∈ pair12Boundaries D)
    (hxy : b.x < c.x) : c.y < b.y :=
  pair12_y_lt_of_x_lt hD hb hc hxy

example {D : Finset Point3} (hD : IsDownset D) {b : Point3}
    (hb : b ∈ pair12Boundaries D) : pair12Rank D b + 1 ≤ b.x :=
  pair12_rank_succ_le_x hD hb

example {D : Finset Point3} (hD : IsDownset D) {b : Point3}
    (hb : b ∈ pair12Boundaries D) : pair12Count D - pair12Rank D b ≤ b.y :=
  pair12_count_sub_rank_le_y hD hb

example {D : Finset Point3} (hD : IsDownset D) {b : Point3}
    (hb : b ∈ pair12Boundaries D) : pair12Count D < b.x + b.y :=
  pair12_count_lt_coord_sum hD hb

example {D : Finset Point3} (hD : IsDownset D) {a : ℕ}
    (ha : MinimalComplement D ⟨a, 0, 0⟩) (hpa : Pure1 ⟨a, 0, 0⟩) :
    pair12Count D + 1 ≤ a :=
  pair12_pure1_intercept_lower hD ha hpa

example {D : Finset Point3} (hD : IsDownset D) {a : ℕ}
    (ha : MinimalComplement D ⟨0, a, 0⟩) (hpa : Pure2 ⟨0, a, 0⟩) :
    pair12Count D + 1 ≤ a :=
  pair12_pure2_intercept_lower hD ha hpa

example {D : Finset Point3} (hD : IsDownset D) {x y : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y ≤ pair12Count D) :
    Point3.mk x y 0 ∈ D :=
  pair12Triangle_subset hD hx hy hxy

example {D : Finset Point3} (hD : IsDownset D) {x y : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x + y = pair12Count D) :
    Point3.mk x y 0 ∈ D :=
  pair12Triangle_subset hD hx hy hxy.le

example {x y : ℕ} (hx : 0 < x) (hy : 0 < y) : ¬ x + y ≤ 0 := by omega
example {x y : ℕ} (hx : 0 < x) (hy : 0 < y) : ¬ x + y ≤ 1 := by omega

example {D : Finset Point3} (hD : IsDownset D) {a : ℕ}
    (ha : MinimalComplement D ⟨a, 0, 0⟩) (hpa : Pure1 ⟨a, 0, 0⟩) :
    pair13Count D + 1 ≤ a :=
  pair13_pure1_intercept_lower hD ha hpa

example {D : Finset Point3} (hD : IsDownset D) {a : ℕ}
    (ha : MinimalComplement D ⟨0, 0, a⟩) (hpa : Pure3 ⟨0, 0, a⟩) :
    pair13Count D + 1 ≤ a :=
  pair13_pure3_intercept_lower hD ha hpa

example {D : Finset Point3} (hD : IsDownset D) {a : ℕ}
    (ha : MinimalComplement D ⟨0, a, 0⟩) (hpa : Pure2 ⟨0, a, 0⟩) :
    pair23Count D + 1 ≤ a :=
  pair23_pure2_intercept_lower hD ha hpa

example {D : Finset Point3} (hD : IsDownset D) {a : ℕ}
    (ha : MinimalComplement D ⟨0, 0, a⟩) (hpa : Pure3 ⟨0, 0, a⟩) :
    pair23Count D + 1 ≤ a :=
  pair23_pure3_intercept_lower hD ha hpa

example {D : Finset Point3} (hD : IsDownset D) {x z : ℕ}
    (hx : 0 < x) (hz : 0 < z) (hxz : x + z ≤ pair13Count D) :
    Point3.mk x 0 z ∈ D :=
  pair13Triangle_subset hD hx hz hxz

example {D : Finset Point3} (hD : IsDownset D) {y z : ℕ}
    (hy : 0 < y) (hz : 0 < z) (hyz : y + z ≤ pair23Count D) :
    Point3.mk 0 y z ∈ D :=
  pair23Triangle_subset hD hy hz hyz

end NSP3
