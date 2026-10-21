import NSP3.SimplexPolynomial

namespace NSP3

def Pair12PlaneExact (S : CyclicStaircase) : Prop :=
  ∀ x y : ℕ, 0 < x → 0 < y →
    (Point3.mk x y 0 ∈ S.D ↔ x + y ≤ pair12Count S.D)

def Pair13PlaneExact (S : CyclicStaircase) : Prop :=
  ∀ x z : ℕ, 0 < x → 0 < z →
    (Point3.mk x 0 z ∈ S.D ↔ x + z ≤ pair13Count S.D)

def Pair23PlaneExact (S : CyclicStaircase) : Prop :=
  ∀ y z : ℕ, 0 < y → 0 < z →
    (Point3.mk 0 y z ∈ S.D ↔ y + z ≤ pair23Count S.D)

noncomputable def pair12ExactBoundary (S : CyclicStaircase) (hexact : Pair12PlaneExact S)
    (i : Fin (pair12Count S.D)) : Pair12Boundary S := by
  let q := pair12Count S.D
  let b : Point3 := ⟨i.1 + 1, q - i.1, 0⟩
  have hiy : 0 < q - i.1 := by dsimp [q]; omega
  have hmin : MinimalComplement S.D b := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hb
      have hsum := (hexact (i.1 + 1) (q - i.1) (by omega) hiy).mp hb
      dsimp [q] at hsum ⊢
      omega
    · intro _
      change Point3.mk i.1 (q - i.1) 0 ∈ S.D
      by_cases hi : i.1 = 0
      · have haxis := (pure2_axis_mem_iff S q).mpr (show q < pure2Intercept S by
          have h := pair12_intercept2_lower S
          omega)
        simpa [hi] using haxis
      · apply (hexact i.1 (q - i.1) (Nat.pos_of_ne_zero hi) hiy).mpr
        omega
    · intro _
      change Point3.mk (i.1 + 1) (q - i.1 - 1) 0 ∈ S.D
      by_cases hy : q - i.1 = 1
      · have haxis : Point3.mk q 0 0 ∈ S.D := by
          apply (pure1_axis_mem_iff S q).mpr
          have h := pair12_intercept1_lower S
          omega
        have hiq : i.1 + 1 = q := by omega
        simpa [hy, hiq] using haxis
      · have hypos : 0 < q - i.1 - 1 := by omega
        apply (hexact (i.1 + 1) (q - i.1 - 1) (by omega) hypos).mpr
        omega
    · simp [b]
  refine ⟨b, hmin, ?_⟩
  exact ⟨by simp [b], by simp [b, hiy]⟩

noncomputable def pair13ExactBoundary (S : CyclicStaircase) (hexact : Pair13PlaneExact S)
    (i : Fin (pair13Count S.D)) : Pair13Boundary S := by
  let q := pair13Count S.D
  let b : Point3 := ⟨i.1 + 1, 0, q - i.1⟩
  have hiz : 0 < q - i.1 := by dsimp [q]; omega
  have hmin : MinimalComplement S.D b := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hb
      have hsum := (hexact (i.1 + 1) (q - i.1) (by omega) hiz).mp hb
      dsimp [q] at hsum ⊢
      omega
    · intro _
      change Point3.mk i.1 0 (q - i.1) ∈ S.D
      by_cases hi : i.1 = 0
      · have haxis := (pure3_axis_mem_iff S q).mpr (show q < pure3Intercept S by
          have h := pair13_intercept3_lower S
          omega)
        simpa [hi] using haxis
      · apply (hexact i.1 (q - i.1) (Nat.pos_of_ne_zero hi) hiz).mpr
        omega
    · simp [b]
    · intro _
      change Point3.mk (i.1 + 1) 0 (q - i.1 - 1) ∈ S.D
      by_cases hz : q - i.1 = 1
      · have haxis : Point3.mk q 0 0 ∈ S.D := by
          apply (pure1_axis_mem_iff S q).mpr
          have h := pair13_intercept1_lower S
          omega
        have hiq : i.1 + 1 = q := by omega
        simpa [hz, hiq] using haxis
      · have hzpos : 0 < q - i.1 - 1 := by omega
        apply (hexact (i.1 + 1) (q - i.1 - 1) (by omega) hzpos).mpr
        omega
  refine ⟨b, hmin, ?_⟩
  exact ⟨by simp [b], by simp [b, hiz]⟩

noncomputable def pair23ExactBoundary (S : CyclicStaircase) (hexact : Pair23PlaneExact S)
    (i : Fin (pair23Count S.D)) : Pair23Boundary S := by
  let q := pair23Count S.D
  let b : Point3 := ⟨0, i.1 + 1, q - i.1⟩
  have hiz : 0 < q - i.1 := by dsimp [q]; omega
  have hmin : MinimalComplement S.D b := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hb
      have hsum := (hexact (i.1 + 1) (q - i.1) (by omega) hiz).mp hb
      dsimp [q] at hsum ⊢
      omega
    · simp [b]
    · intro _
      change Point3.mk 0 i.1 (q - i.1) ∈ S.D
      by_cases hi : i.1 = 0
      · have haxis := (pure3_axis_mem_iff S q).mpr (show q < pure3Intercept S by
          have h := pair23_intercept3_lower S
          omega)
        simpa [hi] using haxis
      · apply (hexact i.1 (q - i.1) (Nat.pos_of_ne_zero hi) hiz).mpr
        omega
    · intro _
      change Point3.mk 0 (i.1 + 1) (q - i.1 - 1) ∈ S.D
      by_cases hz : q - i.1 = 1
      · have haxis : Point3.mk 0 q 0 ∈ S.D := by
          apply (pure2_axis_mem_iff S q).mpr
          have h := pair23_intercept2_lower S
          omega
        have hiq : i.1 + 1 = q := by omega
        simpa [hz, hiq] using haxis
      · have hzpos : 0 < q - i.1 - 1 := by omega
        apply (hexact (i.1 + 1) (q - i.1 - 1) (by omega) hzpos).mpr
        omega
  refine ⟨b, hmin, ?_⟩
  exact ⟨by simp [b], by simp [b, hiz]⟩

noncomputable def pair12ExactReturn (S : CyclicStaircase) (hexact : Pair12PlaneExact S)
    (i : Fin (pair12Count S.D)) : ℕ :=
  pair12ReturnCoord S (pair12ExactBoundary S hexact i)

noncomputable def pair13ExactReturn (S : CyclicStaircase) (hexact : Pair13PlaneExact S)
    (i : Fin (pair13Count S.D)) : ℕ :=
  pair13ReturnCoord S (pair13ExactBoundary S hexact i)

noncomputable def pair23ExactReturn (S : CyclicStaircase) (hexact : Pair23PlaneExact S)
    (i : Fin (pair23Count S.D)) : ℕ :=
  pair23ReturnCoord S (pair23ExactBoundary S hexact i)

theorem pair12ExactReturn_adjacent_ne (S : CyclicStaircase)
    (hexact : Pair12PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair12Count S.D) :
    pair12ExactReturn S hexact ⟨i, by omega⟩ ≠
      pair12ExactReturn S hexact ⟨i + 1, hi⟩ := by
  intro h
  have hb := pair12ReturnCoord_injective S h
  have hx := congrArg (fun b : Pair12Boundary S => b.1.x) hb
  simp [pair12ExactBoundary] at hx

theorem pair13ExactReturn_adjacent_ne (S : CyclicStaircase)
    (hexact : Pair13PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair13Count S.D) :
    pair13ExactReturn S hexact ⟨i, by omega⟩ ≠
      pair13ExactReturn S hexact ⟨i + 1, hi⟩ := by
  intro h
  have hb := pair13ReturnCoord_injective S h
  have hx := congrArg (fun b : Pair13Boundary S => b.1.x) hb
  simp [pair13ExactBoundary] at hx

theorem pair23ExactReturn_adjacent_ne (S : CyclicStaircase)
    (hexact : Pair23PlaneExact S) {i : ℕ}
    (hi : i + 1 < pair23Count S.D) :
    pair23ExactReturn S hexact ⟨i, by omega⟩ ≠
      pair23ExactReturn S hexact ⟨i + 1, hi⟩ := by
  intro h
  have hb := pair23ReturnCoord_injective S h
  have hy := congrArg (fun b : Pair23Boundary S => b.1.y) hb
  simp [pair23ExactBoundary] at hy

end NSP3
