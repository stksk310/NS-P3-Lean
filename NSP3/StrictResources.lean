import NSP3.StrictAccounting
import NSP3.BalancedResources

namespace NSP3

theorem pair12_originFree_capacity (S : CyclicStaircase)
    (hof : Pair12OriginFree S) :
    pair12Count S.D + 1 ≤ pure3Intercept S := by
  classical
  have hcoord (b : Pair12Boundary S) : pair12ReturnCoord S b ∈
      Finset.Ico 1 (pure3Intercept S) := by
    rw [Finset.mem_Ico]
    refine ⟨?_, (pure3_axis_mem_iff S _).mp ?_⟩
    · have hne := hof b
      by_contra h
      apply hne
      apply Point3.ext
      · simpa [Point3.zero] using complementFaceReturn₁ S b.2.1 b.2.2.1
      · simpa [Point3.zero] using complementFaceReturn₂ S b.2.1 b.2.2.2.1
      · simpa [Point3.zero, pair12ReturnCoord] using Nat.eq_zero_of_not_pos h
    · have heq : S.rho b.1 = Point3.mk 0 0 (pair12ReturnCoord S b) := by
        apply Point3.ext
        · exact complementFaceReturn₁ S b.2.1 b.2.2.1
        · exact complementFaceReturn₂ S b.2.1 b.2.2.2.1
        · rfl
      rw [← heq]
      exact S.rho_mem b.1
  let f : Pair12Boundary S → {c : ℕ // c ∈ Finset.Ico 1 (pure3Intercept S)} :=
    fun b => ⟨pair12ReturnCoord S b, hcoord b⟩
  let _ : Fintype {c : ℕ // c ∈ Finset.Ico 1 (pure3Intercept S)} := Fintype.ofFinite _
  have hf : Function.Injective f := fun _ _ h =>
    pair12ReturnCoord_injective S (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective f hf
  have htarget : Fintype.card {c : ℕ // c ∈ Finset.Ico 1 (pure3Intercept S)} =
      pure3Intercept S - 1 := by simp
  rw [card_pair12Boundary, htarget] at hcard
  change pair12Count S.D ≤ pure3Intercept S - 1 at hcard
  have hp := (pure3Intercept_pure S).2.2
  exact Nat.add_one_le_iff.mpr ((Nat.le_sub_one_iff_lt hp).mp hcard)

theorem pair13_originFree_capacity (S : CyclicStaircase)
    (hof : Pair13OriginFree S) :
    pair13Count S.D + 1 ≤ pure2Intercept S := by
  classical
  have hcoord (b : Pair13Boundary S) : pair13ReturnCoord S b ∈
      Finset.Ico 1 (pure2Intercept S) := by
    rw [Finset.mem_Ico]
    refine ⟨?_, (pure2_axis_mem_iff S _).mp ?_⟩
    · have hne := hof b
      by_contra h
      apply hne
      apply Point3.ext
      · simpa [Point3.zero] using complementFaceReturn₁ S b.2.1 b.2.2.1
      · simpa [Point3.zero, pair13ReturnCoord] using Nat.eq_zero_of_not_pos h
      · simpa [Point3.zero] using complementFaceReturn₃ S b.2.1 b.2.2.2.2
    · have heq : S.rho b.1 = Point3.mk 0 (pair13ReturnCoord S b) 0 := by
        apply Point3.ext
        · exact complementFaceReturn₁ S b.2.1 b.2.2.1
        · rfl
        · exact complementFaceReturn₃ S b.2.1 b.2.2.2.2
      rw [← heq]
      exact S.rho_mem b.1
  let f : Pair13Boundary S → {c : ℕ // c ∈ Finset.Ico 1 (pure2Intercept S)} :=
    fun b => ⟨pair13ReturnCoord S b, hcoord b⟩
  let _ : Fintype {c : ℕ // c ∈ Finset.Ico 1 (pure2Intercept S)} := Fintype.ofFinite _
  have hf : Function.Injective f := fun _ _ h =>
    pair13ReturnCoord_injective S (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective f hf
  have htarget : Fintype.card {c : ℕ // c ∈ Finset.Ico 1 (pure2Intercept S)} =
      pure2Intercept S - 1 := by simp
  rw [card_pair13Boundary, htarget] at hcard
  change pair13Count S.D ≤ pure2Intercept S - 1 at hcard
  have hp := (pure2Intercept_pure S).2.1
  exact Nat.add_one_le_iff.mpr ((Nat.le_sub_one_iff_lt hp).mp hcard)

theorem pair23_originFree_capacity (S : CyclicStaircase)
    (hof : Pair23OriginFree S) :
    pair23Count S.D + 1 ≤ pure1Intercept S := by
  classical
  have hcoord (b : Pair23Boundary S) : pair23ReturnCoord S b ∈
      Finset.Ico 1 (pure1Intercept S) := by
    rw [Finset.mem_Ico]
    refine ⟨?_, (pure1_axis_mem_iff S _).mp ?_⟩
    · have hne := hof b
      by_contra h
      apply hne
      apply Point3.ext
      · simpa [Point3.zero, pair23ReturnCoord] using Nat.eq_zero_of_not_pos h
      · simpa [Point3.zero] using complementFaceReturn₂ S b.2.1 b.2.2.2.1
      · simpa [Point3.zero] using complementFaceReturn₃ S b.2.1 b.2.2.2.2
    · have heq : S.rho b.1 = Point3.mk (pair23ReturnCoord S b) 0 0 := by
        apply Point3.ext
        · rfl
        · exact complementFaceReturn₂ S b.2.1 b.2.2.2.1
        · exact complementFaceReturn₃ S b.2.1 b.2.2.2.2
      rw [← heq]
      exact S.rho_mem b.1
  let f : Pair23Boundary S → {c : ℕ // c ∈ Finset.Ico 1 (pure1Intercept S)} :=
    fun b => ⟨pair23ReturnCoord S b, hcoord b⟩
  let _ : Fintype {c : ℕ // c ∈ Finset.Ico 1 (pure1Intercept S)} := Fintype.ofFinite _
  have hf : Function.Injective f := fun _ _ h =>
    pair23ReturnCoord_injective S (congrArg Subtype.val h)
  have hcard := Fintype.card_le_of_injective f hf
  have htarget : Fintype.card {c : ℕ // c ∈ Finset.Ico 1 (pure1Intercept S)} =
      pure1Intercept S - 1 := by simp
  rw [card_pair23Boundary, htarget] at hcard
  change pair23Count S.D ≤ pure1Intercept S - 1 at hcard
  have hp := (pure1Intercept_pure S).1
  exact Nat.add_one_le_iff.mpr ((Nat.le_sub_one_iff_lt hp).mp hcard)

theorem pair12_originFree_strict_resource (S : CyclicStaircase)
    (hof : Pair12OriginFree S) : 1 ≤ strictAxisExcess3 S := by
  have hcap := pair12_originFree_capacity S hof
  unfold strictAxisExcess3
  omega

private theorem strict_bounded_sequence_no_span {R r g : ℕ}
    (hR : 2 ≤ R) (hspan : r - 1 < g * (R - 1)) (f : Fin R → ℕ)
    (hlo : ∀ i, 1 ≤ f i) (hhi : ∀ i, f i ≤ r)
    (hne : ∀ {i : ℕ} (hi : i + 1 < R), f ⟨i, by omega⟩ ≠ f ⟨i + 1, hi⟩)
    (hup : ∀ {i : ℕ} (hi : i + 1 < R),
      f ⟨i, by omega⟩ < f ⟨i + 1, hi⟩ → g ≤ f ⟨i + 1, hi⟩ - f ⟨i, by omega⟩)
    (hdown : ∀ {i : ℕ} (hi : i + 1 < R),
      f ⟨i + 1, hi⟩ < f ⟨i, by omega⟩ → r ≤ f ⟨i, by omega⟩ - f ⟨i + 1, hi⟩) : False := by
  have hadj {i : ℕ} (hi : i + 1 < R) : f ⟨i, by omega⟩ < f ⟨i + 1, hi⟩ := by
    rcases lt_trichotomy (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩) with h | h | h
    · exact h
    · exact False.elim ((hne hi) h)
    · have hd := hdown hi h
      have hu := hhi ⟨i, by omega⟩
      have hl := hlo ⟨i + 1, hi⟩
      omega
  have hgrowth : ∀ n : ℕ, (hn : n < R) → 1 + g * n ≤ f ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero => intro hn; simpa using hlo ⟨0, hn⟩
    | succ n ih =>
      intro hn
      have hn0 : n < R := by omega
      have hprev := ih hn0
      have hadj' := hadj hn
      have hgap := hup (i := n) hn hadj'
      change 1 + g * n ≤ f ⟨n, hn0⟩ at hprev
      change g ≤ f ⟨n + 1, hn⟩ - f ⟨n, hn0⟩ at hgap
      change f ⟨n, hn0⟩ < f ⟨n + 1, hn⟩ at hadj'
      have hcancel :
          (f ⟨n + 1, hn⟩ - f ⟨n, hn0⟩) + f ⟨n, hn0⟩ = f ⟨n + 1, hn⟩ :=
        Nat.sub_add_cancel (Nat.le_of_lt hadj')
      calc
        1 + g * (n + 1) = (1 + g * n) + g := by
          simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        _ ≤ f ⟨n, hn0⟩ + g := Nat.add_le_add_right hprev g
        _ = g + f ⟨n, hn0⟩ := Nat.add_comm _ _
        _ ≤ (f ⟨n + 1, hn⟩ - f ⟨n, hn0⟩) + f ⟨n, hn0⟩ :=
          Nat.add_le_add_right hgap _
        _ = f ⟨n + 1, hn⟩ := hcancel
  have hi : R - 1 < R := by omega
  have hl := hgrowth (R - 1) hi
  have hu := hhi ⟨R - 1, hi⟩
  omega

private theorem pair13ExactBoundary_rho_axis_strict (S : CyclicStaircase)
    (hexact : Pair13PlaneExact S) (i : Fin (pair13Count S.D)) :
    S.rho (pair13ExactBoundary S hexact i).1 = Point3.mk 0 (pair13ExactReturn S hexact i) 0 := by
  apply Point3.ext
  · exact complementFaceReturn₁ S (pair13ExactBoundary S hexact i).2.1
      (pair13ExactBoundary S hexact i).2.2.1
  · rfl
  · exact complementFaceReturn₃ S (pair13ExactBoundary S hexact i).2.1
      (pair13ExactBoundary S hexact i).2.2.2.2

private theorem pair23ExactBoundary_rho_axis_strict (S : CyclicStaircase)
    (hexact : Pair23PlaneExact S) (i : Fin (pair23Count S.D)) :
    S.rho (pair23ExactBoundary S hexact i).1 = Point3.mk (pair23ExactReturn S hexact i) 0 0 := by
  apply Point3.ext
  · rfl
  · exact complementFaceReturn₂ S (pair23ExactBoundary S hexact i).2.1
      (pair23ExactBoundary S hexact i).2.2.2.1
  · exact complementFaceReturn₃ S (pair23ExactBoundary S hexact i).2.1
      (pair23ExactBoundary S hexact i).2.2.2.2

theorem pair13_originFree_strict_resource (S : CyclicStaircase)
    (hs : 2 ≤ pair13Count S.D)
    (hspan : pair12Count S.D - 1 < pair23Count S.D * (pair13Count S.D - 1))
    (hof : Pair13OriginFree S) :
    1 ≤ strictAxisExcess2 S + (pair13ExtraFinset S).card := by
  by_contra hnot
  have haxis : strictAxisExcess2 S = 0 := by omega
  have hextra : (pair13ExtraFinset S).card = 0 := by omega
  have hbase := strict_axis2_baseline S
  have haxisEq : pure2Intercept S = pair12Count S.D + 1 := by
    unfold strictAxisExcess2 at haxis
    omega
  have hexact := pair13PlaneExact_of_extra_card_eq_zero S hextra
  let f : Fin (pair13Count S.D) → ℕ := pair13ExactReturn S hexact
  have hlo (i : Fin (pair13Count S.D)) : 1 ≤ f i := by
    have hrho := pair13ExactBoundary_rho_axis_strict S hexact i
    have hne := hof (pair13ExactBoundary S hexact i)
    by_contra h
    apply hne
    rw [hrho]
    apply Point3.ext <;> simp [Point3.zero, f, Nat.eq_zero_of_not_pos h]
  have hhi (i : Fin (pair13Count S.D)) : f i ≤ pair12Count S.D := by
    have hrho := pair13ExactBoundary_rho_axis_strict S hexact i
    have hm : Point3.mk 0 (f i) 0 ∈ S.D := by rw [← hrho]; exact S.rho_mem _
    have := (pure2_axis_mem_iff S (f i)).mp hm
    omega
  exact strict_bounded_sequence_no_span hs hspan f hlo hhi
    (fun hi => pair13ExactReturn_adjacent_ne S hexact hi)
    (fun hi h => pair13ExactReturn_step_up S hexact hi h)
    (fun hi h => pair13ExactReturn_step_down S hexact hi h)

theorem pair23_originFree_strict_resource (S : CyclicStaircase)
    (ht : 2 ≤ pair23Count S.D)
    (hspan : pair12Count S.D - 1 < pair13Count S.D * (pair23Count S.D - 1))
    (hof : Pair23OriginFree S) :
    1 ≤ strictAxisExcess1 S + (pair23ExtraFinset S).card := by
  by_contra hnot
  have haxis : strictAxisExcess1 S = 0 := by omega
  have hextra : (pair23ExtraFinset S).card = 0 := by omega
  have hbase := strict_axis1_baseline S
  have haxisEq : pure1Intercept S = pair12Count S.D + 1 := by
    unfold strictAxisExcess1 at haxis
    omega
  have hexact := pair23PlaneExact_of_extra_card_eq_zero S hextra
  let f : Fin (pair23Count S.D) → ℕ := pair23ExactReturn S hexact
  have hlo (i : Fin (pair23Count S.D)) : 1 ≤ f i := by
    have hrho := pair23ExactBoundary_rho_axis_strict S hexact i
    have hne := hof (pair23ExactBoundary S hexact i)
    by_contra h
    apply hne
    rw [hrho]
    apply Point3.ext <;> simp [Point3.zero, f, Nat.eq_zero_of_not_pos h]
  have hhi (i : Fin (pair23Count S.D)) : f i ≤ pair12Count S.D := by
    have hrho := pair23ExactBoundary_rho_axis_strict S hexact i
    have hm : Point3.mk (f i) 0 0 ∈ S.D := by rw [← hrho]; exact S.rho_mem _
    have := (pure1_axis_mem_iff S (f i)).mp hm
    omega
  exact strict_bounded_sequence_no_span ht hspan f hlo hhi
    (fun hi => pair23ExactReturn_adjacent_ne S hexact hi)
    (fun hi h => pair23ExactReturn_step_up S hexact hi h)
    (fun hi h => pair23ExactReturn_step_down S hexact hi h)

end NSP3
