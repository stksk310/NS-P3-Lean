import NSP3.BalancedAccounting

namespace NSP3

def Pair12OriginFree (S : CyclicStaircase) : Prop :=
  ∀ b : Pair12Boundary S, S.rho b.1 ≠ Point3.zero

def Pair13OriginFree (S : CyclicStaircase) : Prop :=
  ∀ b : Pair13Boundary S, S.rho b.1 ≠ Point3.zero

def Pair23OriginFree (S : CyclicStaircase) : Prop :=
  ∀ b : Pair23Boundary S, S.rho b.1 ≠ Point3.zero

private theorem bounded_sequence_no_long {R t : ℕ}
    (hR : 2 ≤ R) (ht : 2 ≤ t) (f : Fin R → ℕ)
    (hlo : ∀ i, 1 ≤ f i) (hhi : ∀ i, f i ≤ R)
    (hne : ∀ {i : ℕ} (hi : i + 1 < R),
      f ⟨i, by omega⟩ ≠ f ⟨i + 1, hi⟩)
    (hup : ∀ {i : ℕ} (hi : i + 1 < R),
      f ⟨i, by omega⟩ < f ⟨i + 1, hi⟩ →
        t ≤ f ⟨i + 1, hi⟩ - f ⟨i, by omega⟩)
    (hdown : ∀ {i : ℕ} (hi : i + 1 < R),
      f ⟨i + 1, hi⟩ < f ⟨i, by omega⟩ →
        R ≤ f ⟨i, by omega⟩ - f ⟨i + 1, hi⟩) : False := by
  have hadj_up {i : ℕ} (hi : i + 1 < R) :
      f ⟨i, by omega⟩ < f ⟨i + 1, hi⟩ := by
    rcases lt_trichotomy (f ⟨i, by omega⟩) (f ⟨i + 1, hi⟩) with hlt | heq | hgt
    · exact hlt
    · exact False.elim ((hne hi) heq)
    · have hd := hdown hi hgt
      have hu := hhi ⟨i, by omega⟩
      have hl := hlo ⟨i + 1, hi⟩
      omega
  have hgrowth : ∀ n : ℕ, (hn : n < R) → 1 + t * n ≤ f ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
        intro hn
        simpa using hlo ⟨0, hn⟩
    | succ n ih =>
        intro hn
        have hn0 : n < R := by omega
        have hi : n + 1 < R := by omega
        have hprev := ih hn0
        have hlt := hadj_up hi
        have hgap := hup hi hlt
        rw [Nat.mul_succ]
        omega
  have hlastIndex : R - 1 < R := by omega
  have hlast := hgrowth (R - 1) hlastIndex
  have hlastUpper := hhi ⟨R - 1, hlastIndex⟩
  have hmul := Nat.mul_le_mul_right (R - 1) ht
  omega

private theorem pair12ExactBoundary_rho_axis (S : CyclicStaircase)
    (hexact : Pair12PlaneExact S) (i : Fin (pair12Count S.D)) :
    S.rho (pair12ExactBoundary S hexact i).1 =
      Point3.mk 0 0 (pair12ExactReturn S hexact i) := by
  apply Point3.ext
  · exact complementFaceReturn₁ S (pair12ExactBoundary S hexact i).2.1
      (pair12ExactBoundary S hexact i).2.2.1
  · exact complementFaceReturn₂ S (pair12ExactBoundary S hexact i).2.1
      (pair12ExactBoundary S hexact i).2.2.2.1
  · rfl

private theorem pair13ExactBoundary_rho_axis (S : CyclicStaircase)
    (hexact : Pair13PlaneExact S) (i : Fin (pair13Count S.D)) :
    S.rho (pair13ExactBoundary S hexact i).1 =
      Point3.mk 0 (pair13ExactReturn S hexact i) 0 := by
  apply Point3.ext
  · exact complementFaceReturn₁ S (pair13ExactBoundary S hexact i).2.1
      (pair13ExactBoundary S hexact i).2.2.1
  · rfl
  · exact complementFaceReturn₃ S (pair13ExactBoundary S hexact i).2.1
      (pair13ExactBoundary S hexact i).2.2.2.2

private theorem pair23ExactBoundary_rho_axis (S : CyclicStaircase)
    (hexact : Pair23PlaneExact S) (i : Fin (pair23Count S.D)) :
    S.rho (pair23ExactBoundary S hexact i).1 =
      Point3.mk (pair23ExactReturn S hexact i) 0 0 := by
  apply Point3.ext
  · rfl
  · exact complementFaceReturn₂ S (pair23ExactBoundary S hexact i).2.1
      (pair23ExactBoundary S hexact i).2.2.2.1
  · exact complementFaceReturn₃ S (pair23ExactBoundary S hexact i).2.1
      (pair23ExactBoundary S hexact i).2.2.2.2

theorem pair12_originFree_resource (S : CyclicStaircase)
    (_hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D)
    (ht : 2 ≤ pair23Count S.D) (hof : Pair12OriginFree S) :
    1 ≤ balancedAxisExcess3 S + (pair12ExtraFinset S).card := by
  by_contra hnot
  have hsum : balancedAxisExcess3 S + (pair12ExtraFinset S).card = 0 := by omega
  have haxis : balancedAxisExcess3 S = 0 := by omega
  have hextra : (pair12ExtraFinset S).card = 0 := by omega
  have hbase := balanced_axis3_baseline S heq
  have haxisEq : pure3Intercept S = pair12Count S.D + 1 := by
    unfold balancedAxisExcess3 at haxis
    omega
  have hexact := pair12PlaneExact_of_extra_card_eq_zero S hextra
  have hR : 2 ≤ pair12Count S.D := by
    have horder := hord.1
    omega
  let f : Fin (pair12Count S.D) → ℕ := pair12ExactReturn S hexact
  have hlo (i : Fin (pair12Count S.D)) : 1 ≤ f i := by
    have hrho := pair12ExactBoundary_rho_axis S hexact i
    have hne := hof (pair12ExactBoundary S hexact i)
    have hcne : f i ≠ 0 := by
      intro hc
      apply hne
      rw [hrho]
      apply Point3.ext <;> simp [Point3.zero, f, hc]
    omega
  have hhi (i : Fin (pair12Count S.D)) : f i ≤ pair12Count S.D := by
    have hrho := pair12ExactBoundary_rho_axis S hexact i
    have hmem : Point3.mk 0 0 (f i) ∈ S.D := by
      rw [← hrho]
      exact S.rho_mem (pair12ExactBoundary S hexact i).1
    have hlt := (pure3_axis_mem_iff S (f i)).mp hmem
    omega
  exact bounded_sequence_no_long hR ht f hlo hhi
    (fun hi => pair12ExactReturn_adjacent_ne S hexact hi)
    (fun hi hlt => pair12ExactReturn_step_up S hexact hi hlt)
    (fun hi hlt => by
      simpa [f, heq] using pair12ExactReturn_step_down S hexact hi hlt)

theorem pair13_originFree_resource (S : CyclicStaircase)
    (_hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D)
    (ht : 2 ≤ pair23Count S.D) (hof : Pair13OriginFree S) :
    1 ≤ balancedAxisExcess2 S + (pair13ExtraFinset S).card := by
  by_contra hnot
  have hsum : balancedAxisExcess2 S + (pair13ExtraFinset S).card = 0 := by omega
  have haxis : balancedAxisExcess2 S = 0 := by omega
  have hextra : (pair13ExtraFinset S).card = 0 := by omega
  have hbase := balanced_axis2_baseline S
  have haxisEq : pure2Intercept S = pair12Count S.D + 1 := by
    unfold balancedAxisExcess2 at haxis
    omega
  have hexact := pair13PlaneExact_of_extra_card_eq_zero S hextra
  have hR : 2 ≤ pair13Count S.D := by
    have horder := hord.1
    omega
  let f : Fin (pair13Count S.D) → ℕ := pair13ExactReturn S hexact
  have hlo (i : Fin (pair13Count S.D)) : 1 ≤ f i := by
    have hrho := pair13ExactBoundary_rho_axis S hexact i
    have hne := hof (pair13ExactBoundary S hexact i)
    have hcne : f i ≠ 0 := by
      intro hc
      apply hne
      rw [hrho]
      apply Point3.ext <;> simp [Point3.zero, f, hc]
    omega
  have hhi (i : Fin (pair13Count S.D)) : f i ≤ pair13Count S.D := by
    have hrho := pair13ExactBoundary_rho_axis S hexact i
    have hmem : Point3.mk 0 (f i) 0 ∈ S.D := by
      rw [← hrho]
      exact S.rho_mem (pair13ExactBoundary S hexact i).1
    have hlt := (pure2_axis_mem_iff S (f i)).mp hmem
    omega
  exact bounded_sequence_no_long hR ht f hlo hhi
    (fun hi => pair13ExactReturn_adjacent_ne S hexact hi)
    (fun hi hlt => pair13ExactReturn_step_up S hexact hi hlt)
    (fun hi hlt => by
      simpa [f, heq] using pair13ExactReturn_step_down S hexact hi hlt)

theorem pair23_originFree_resource (S : CyclicStaircase)
    (_hnf : NoFullSupportBoundary S) (_hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D)
    (ht : 2 ≤ pair23Count S.D) (hof : Pair23OriginFree S) :
    1 ≤ balancedAxisExcess1 S + (pair23ExtraFinset S).card := by
  by_contra hnot
  have hsum : balancedAxisExcess1 S + (pair23ExtraFinset S).card = 0 := by omega
  have haxis : balancedAxisExcess1 S = 0 := by omega
  have hextra : (pair23ExtraFinset S).card = 0 := by omega
  have hbase := balanced_axis1_baseline S
  have haxisEq : pure1Intercept S = pair12Count S.D + 1 := by
    unfold balancedAxisExcess1 at haxis
    omega
  have hexact := pair23PlaneExact_of_extra_card_eq_zero S hextra
  let i0 : Fin (pair23Count S.D) := ⟨0, by omega⟩
  let i1 : Fin (pair23Count S.D) := ⟨1, by omega⟩
  let c0 := pair23ExactReturn S hexact i0
  let c1 := pair23ExactReturn S hexact i1
  have hbounds (i : Fin (pair23Count S.D)) :
      1 ≤ pair23ExactReturn S hexact i ∧ pair23ExactReturn S hexact i ≤ pair12Count S.D := by
    have hrho := pair23ExactBoundary_rho_axis S hexact i
    have hne := hof (pair23ExactBoundary S hexact i)
    have hcne : pair23ExactReturn S hexact i ≠ 0 := by
      intro hc
      apply hne
      rw [hrho]
      apply Point3.ext <;> simp [Point3.zero, hc]
    have hmem : Point3.mk (pair23ExactReturn S hexact i) 0 0 ∈ S.D := by
      rw [← hrho]
      exact S.rho_mem (pair23ExactBoundary S hexact i).1
    have hlt := (pure1_axis_mem_iff S _).mp hmem
    omega
  have hb0 := hbounds i0
  have hb1 := hbounds i1
  change 1 ≤ c0 ∧ c0 ≤ pair12Count S.D at hb0
  change 1 ≤ c1 ∧ c1 ≤ pair12Count S.D at hb1
  have hne : c0 ≠ c1 := by
    simpa [c0, c1, i0, i1] using pair23ExactReturn_adjacent_ne S hexact (i := 0) (by omega)
  rcases lt_trichotomy c0 c1 with hlt | heqc | hgt
  · have hgap := pair23ExactReturn_step_up S hexact (i := 0) (by omega) (by
      simpa [c0, c1, i0, i1] using hlt)
    change pair13Count S.D ≤ c1 - c0 at hgap
    omega
  · exact hne heqc
  · have hgap := pair23ExactReturn_step_down S hexact (i := 0) (by omega) (by
      simpa [c0, c1, i0, i1] using hgt)
    change pair12Count S.D ≤ c0 - c1 at hgap
    omega

theorem two_pairFamilies_originFree (S : CyclicStaircase)
    (_hnf : NoFullSupportBoundary S) :
    (Pair12OriginFree S ∧ Pair13OriginFree S) ∨
      (Pair12OriginFree S ∧ Pair23OriginFree S) ∨
      (Pair13OriginFree S ∧ Pair23OriginFree S) := by
  classical
  by_cases h12 : Pair12OriginFree S
  · by_cases h13 : Pair13OriginFree S
    · exact Or.inl ⟨h12, h13⟩
    · by_cases h23 : Pair23OriginFree S
      · exact Or.inr (Or.inl ⟨h12, h23⟩)
      · have h13' : ∃ b : Pair13Boundary S, S.rho b.1 = Point3.zero := by
          simpa [Pair13OriginFree] using h13
        have h23' : ∃ b : Pair23Boundary S, S.rho b.1 = Point3.zero := by
          simpa [Pair23OriginFree] using h23
        obtain ⟨b13, hb13⟩ := h13'
        obtain ⟨b23, hb23⟩ := h23'
        exact False.elim ((pair13_pair23_returns_ne S
          b13.2.1 b13.2.2 b23.2.1 b23.2.2) (hb13.trans hb23.symm))
  · by_cases h13 : Pair13OriginFree S
    · by_cases h23 : Pair23OriginFree S
      · exact Or.inr (Or.inr ⟨h13, h23⟩)
      · have h12' : ∃ b : Pair12Boundary S, S.rho b.1 = Point3.zero := by
          simpa [Pair12OriginFree] using h12
        have h23' : ∃ b : Pair23Boundary S, S.rho b.1 = Point3.zero := by
          simpa [Pair23OriginFree] using h23
        obtain ⟨b12, hb12⟩ := h12'
        obtain ⟨b23, hb23⟩ := h23'
        exact False.elim ((pair12_pair23_returns_ne S
          b12.2.1 b12.2.2 b23.2.1 b23.2.2) (hb12.trans hb23.symm))
    · have h12' : ∃ b : Pair12Boundary S, S.rho b.1 = Point3.zero := by
        simpa [Pair12OriginFree] using h12
      have h13' : ∃ b : Pair13Boundary S, S.rho b.1 = Point3.zero := by
        simpa [Pair13OriginFree] using h13
      obtain ⟨b12, hb12⟩ := h12'
      obtain ⟨b13, hb13⟩ := h13'
      exact False.elim ((pair12_pair13_returns_ne S
        b12.2.1 b12.2.2 b13.2.1 b13.2.2) (hb12.trans hb13.symm))

end NSP3
