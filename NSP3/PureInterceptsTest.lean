import NSP3.PureIntercepts

namespace NSP3

example (S : CyclicStaircase) : S.D.Nonempty := S.nonempty_D

example (S : CyclicStaircase) :
    MinimalComplement S.D ⟨pure1Intercept S, 0, 0⟩ :=
  pure1Intercept_minimalComplement S

example (S : CyclicStaircase) : Pure1 ⟨pure1Intercept S, 0, 0⟩ :=
  pure1Intercept_pure S

example (S : CyclicStaircase) :
    MinimalComplement S.D ⟨0, pure2Intercept S, 0⟩ :=
  pure2Intercept_minimalComplement S

example (S : CyclicStaircase) : Pure2 ⟨0, pure2Intercept S, 0⟩ :=
  pure2Intercept_pure S

example (S : CyclicStaircase) :
    MinimalComplement S.D ⟨0, 0, pure3Intercept S⟩ :=
  pure3Intercept_minimalComplement S

example (S : CyclicStaircase) : Pure3 ⟨0, 0, pure3Intercept S⟩ :=
  pure3Intercept_pure S

example (S : CyclicStaircase) {a : ℕ}
    (ha : MinimalComplement S.D ⟨a, 0, 0⟩) (hp : Pure1 ⟨a, 0, 0⟩) :
    a = pure1Intercept S :=
  pure1_minimalComplement_eq_intercept S ha hp

example (S : CyclicStaircase) {a : ℕ}
    (ha : MinimalComplement S.D ⟨0, a, 0⟩) (hp : Pure2 ⟨0, a, 0⟩) :
    a = pure2Intercept S :=
  pure2_minimalComplement_eq_intercept S ha hp

example (S : CyclicStaircase) {a : ℕ}
    (ha : MinimalComplement S.D ⟨0, 0, a⟩) (hp : Pure3 ⟨0, 0, a⟩) :
    a = pure3Intercept S :=
  pure3_minimalComplement_eq_intercept S ha hp

example (S : CyclicStaircase) (c : ℕ) :
    Point3.mk c 0 0 ∈ S.D ↔ c < pure1Intercept S :=
  pure1_axis_mem_iff S c

example (S : CyclicStaircase) (c : ℕ) :
    Point3.mk 0 c 0 ∈ S.D ↔ c < pure2Intercept S :=
  pure2_axis_mem_iff S c

example (S : CyclicStaircase) (c : ℕ) :
    Point3.mk 0 0 c ∈ S.D ↔ c < pure3Intercept S :=
  pure3_axis_mem_iff S c

example (S : CyclicStaircase) :
    Point3.mk (pure1Intercept S) 0 0 ∉ S.D := by
  rw [pure1_axis_mem_iff]
  omega

example (S : CyclicStaircase) : Point3.mk 0 0 0 ∈ S.D := by
  rw [pure1_axis_mem_iff]
  exact (pure1Intercept_pure S).1

example (S : CyclicStaircase) :
    Point3.mk (pure1Intercept S + 1) 0 0 ∉ S.D := by
  rw [pure1_axis_mem_iff]
  omega

example (S : CyclicStaircase) :
    Point3.mk 0 (pure2Intercept S) 0 ∉ S.D := by
  rw [pure2_axis_mem_iff]
  omega

example (S : CyclicStaircase) :
    Point3.mk 0 (pure2Intercept S + 1) 0 ∉ S.D := by
  rw [pure2_axis_mem_iff]
  omega

example (S : CyclicStaircase) :
    Point3.mk 0 0 (pure3Intercept S) ∉ S.D := by
  rw [pure3_axis_mem_iff]
  omega

example (S : CyclicStaircase) :
    Point3.mk 0 0 (pure3Intercept S + 1) ∉ S.D := by
  rw [pure3_axis_mem_iff]
  omega

end NSP3
