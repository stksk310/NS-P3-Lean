import NSP3.PairFerrers
import NSP3.Residue

namespace NSP3

namespace CyclicStaircase

/-- The standard set of a cyclic staircase is nonempty. -/
theorem nonempty_D (S : CyclicStaircase) : S.D.Nonempty := by
  rw [← Finset.card_pos, S.card_D]
  exact S.hm

end CyclicStaircase

noncomputable def pure1Intercept (S : CyclicStaircase) : ℕ :=
  Classical.choose (exists_pure1_minimalComplement S.down_closed S.nonempty_D)

noncomputable def pure2Intercept (S : CyclicStaircase) : ℕ :=
  Classical.choose (exists_pure2_minimalComplement S.down_closed S.nonempty_D)

noncomputable def pure3Intercept (S : CyclicStaircase) : ℕ :=
  Classical.choose (exists_pure3_minimalComplement S.down_closed S.nonempty_D)

private theorem pure1Intercept_spec (S : CyclicStaircase) :
    MinimalComplement S.D ⟨pure1Intercept S, 0, 0⟩ ∧
      Pure1 ⟨pure1Intercept S, 0, 0⟩ :=
  Classical.choose_spec (exists_pure1_minimalComplement S.down_closed S.nonempty_D)

private theorem pure2Intercept_spec (S : CyclicStaircase) :
    MinimalComplement S.D ⟨0, pure2Intercept S, 0⟩ ∧
      Pure2 ⟨0, pure2Intercept S, 0⟩ :=
  Classical.choose_spec (exists_pure2_minimalComplement S.down_closed S.nonempty_D)

private theorem pure3Intercept_spec (S : CyclicStaircase) :
    MinimalComplement S.D ⟨0, 0, pure3Intercept S⟩ ∧
      Pure3 ⟨0, 0, pure3Intercept S⟩ :=
  Classical.choose_spec (exists_pure3_minimalComplement S.down_closed S.nonempty_D)

theorem pure1Intercept_minimalComplement (S : CyclicStaircase) :
    MinimalComplement S.D ⟨pure1Intercept S, 0, 0⟩ :=
  (pure1Intercept_spec S).1

theorem pure1Intercept_pure (S : CyclicStaircase) :
    Pure1 ⟨pure1Intercept S, 0, 0⟩ :=
  (pure1Intercept_spec S).2

theorem pure2Intercept_minimalComplement (S : CyclicStaircase) :
    MinimalComplement S.D ⟨0, pure2Intercept S, 0⟩ :=
  (pure2Intercept_spec S).1

theorem pure2Intercept_pure (S : CyclicStaircase) :
    Pure2 ⟨0, pure2Intercept S, 0⟩ :=
  (pure2Intercept_spec S).2

theorem pure3Intercept_minimalComplement (S : CyclicStaircase) :
    MinimalComplement S.D ⟨0, 0, pure3Intercept S⟩ :=
  (pure3Intercept_spec S).1

theorem pure3Intercept_pure (S : CyclicStaircase) :
    Pure3 ⟨0, 0, pure3Intercept S⟩ :=
  (pure3Intercept_spec S).2

theorem pure1_minimalComplement_eq_intercept (S : CyclicStaircase) {a : ℕ}
    (ha : MinimalComplement S.D ⟨a, 0, 0⟩) (_hp : Pure1 ⟨a, 0, 0⟩) :
    a = pure1Intercept S := by
  by_contra hne
  have hinc := minimalComplements_incomparable S.down_closed ha
    (pure1Intercept_minimalComplement S) (by intro h; exact hne (congrArg Point3.x h))
  rcases Nat.le_total a (pure1Intercept S) with hle | hle
  · exact hinc.1 ⟨hle, Nat.zero_le _, Nat.zero_le _⟩
  · exact hinc.2 ⟨hle, Nat.zero_le _, Nat.zero_le _⟩

theorem pure2_minimalComplement_eq_intercept (S : CyclicStaircase) {a : ℕ}
    (ha : MinimalComplement S.D ⟨0, a, 0⟩) (_hp : Pure2 ⟨0, a, 0⟩) :
    a = pure2Intercept S := by
  by_contra hne
  have hinc := minimalComplements_incomparable S.down_closed ha
    (pure2Intercept_minimalComplement S) (by intro h; exact hne (congrArg Point3.y h))
  rcases Nat.le_total a (pure2Intercept S) with hle | hle
  · exact hinc.1 ⟨Nat.zero_le _, hle, Nat.zero_le _⟩
  · exact hinc.2 ⟨Nat.zero_le _, hle, Nat.zero_le _⟩

theorem pure3_minimalComplement_eq_intercept (S : CyclicStaircase) {a : ℕ}
    (ha : MinimalComplement S.D ⟨0, 0, a⟩) (_hp : Pure3 ⟨0, 0, a⟩) :
    a = pure3Intercept S := by
  by_contra hne
  have hinc := minimalComplements_incomparable S.down_closed ha
    (pure3Intercept_minimalComplement S) (by intro h; exact hne (congrArg Point3.z h))
  rcases Nat.le_total a (pure3Intercept S) with hle | hle
  · exact hinc.1 ⟨Nat.zero_le _, Nat.zero_le _, hle⟩
  · exact hinc.2 ⟨Nat.zero_le _, Nat.zero_le _, hle⟩

@[simp] theorem pure1_axis_mem_iff (S : CyclicStaircase) (c : ℕ) :
    Point3.mk c 0 0 ∈ S.D ↔ c < pure1Intercept S := by
  constructor
  · intro hc
    by_contra hnot
    have hle : pure1Intercept S ≤ c := Nat.le_of_not_gt hnot
    have hboundary : Point3.mk (pure1Intercept S) 0 0 ∈ S.D :=
      S.down_closed ⟨hle, Nat.zero_le _, Nat.zero_le _⟩ hc
    exact (pure1Intercept_minimalComplement S).not_mem hboundary
  · intro hlt
    have hp := pure1Intercept_pure S
    have hpred := (pure1Intercept_minimalComplement S).pred1_mem hp.1
    apply S.down_closed (b := Point3.pred1 ⟨pure1Intercept S, 0, 0⟩) ?_ hpred
    exact ⟨by simp [Point3.pred1]; omega, by simp [Point3.pred1], by simp [Point3.pred1]⟩

@[simp] theorem pure2_axis_mem_iff (S : CyclicStaircase) (c : ℕ) :
    Point3.mk 0 c 0 ∈ S.D ↔ c < pure2Intercept S := by
  constructor
  · intro hc
    by_contra hnot
    have hle : pure2Intercept S ≤ c := Nat.le_of_not_gt hnot
    have hboundary : Point3.mk 0 (pure2Intercept S) 0 ∈ S.D :=
      S.down_closed ⟨Nat.zero_le _, hle, Nat.zero_le _⟩ hc
    exact (pure2Intercept_minimalComplement S).not_mem hboundary
  · intro hlt
    have hp := pure2Intercept_pure S
    have hpred := (pure2Intercept_minimalComplement S).pred2_mem hp.2.1
    apply S.down_closed (b := Point3.pred2 ⟨0, pure2Intercept S, 0⟩) ?_ hpred
    exact ⟨by simp [Point3.pred2], by simp [Point3.pred2]; omega, by simp [Point3.pred2]⟩

@[simp] theorem pure3_axis_mem_iff (S : CyclicStaircase) (c : ℕ) :
    Point3.mk 0 0 c ∈ S.D ↔ c < pure3Intercept S := by
  constructor
  · intro hc
    by_contra hnot
    have hle : pure3Intercept S ≤ c := Nat.le_of_not_gt hnot
    have hboundary : Point3.mk 0 0 (pure3Intercept S) ∈ S.D :=
      S.down_closed ⟨Nat.zero_le _, Nat.zero_le _, hle⟩ hc
    exact (pure3Intercept_minimalComplement S).not_mem hboundary
  · intro hlt
    have hp := pure3Intercept_pure S
    have hpred := (pure3Intercept_minimalComplement S).pred3_mem hp.2.2
    apply S.down_closed (b := Point3.pred3 ⟨0, 0, pure3Intercept S⟩) ?_ hpred
    exact ⟨by simp [Point3.pred3], by simp [Point3.pred3], by simp [Point3.pred3]; omega⟩

end NSP3
