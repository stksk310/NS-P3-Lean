import NSP3.UnbalancedArithmetic

namespace NSP3

private theorem pair12ExactBoundary_rho_axis_residual (S : CyclicStaircase)
    (hexact : Pair12PlaneExact S) (i : Fin (pair12Count S.D)) :
    S.rho (pair12ExactBoundary S hexact i).1 =
      Point3.mk 0 0 (pair12ExactReturn S hexact i) := by
  apply Point3.ext
  · exact complementFaceReturn₁ S (pair12ExactBoundary S hexact i).2.1
      (pair12ExactBoundary S hexact i).2.2.1
  · exact complementFaceReturn₂ S (pair12ExactBoundary S hexact i).2.1
      (pair12ExactBoundary S hexact i).2.2.2.1
  · rfl

private theorem strict_residual_322_sequence_impossible (S : CyclicStaircase)
    (hr : pair12Count S.D = 3) (hs : pair13Count S.D = 2)
    (ht : pair23Count S.D = 2) (ha3 : pure3Intercept S = 3)
    (hexact : Pair12PlaneExact S) : False := by
  let i0 : Fin (pair12Count S.D) := ⟨0, by omega⟩
  let i1 : Fin (pair12Count S.D) := ⟨1, by omega⟩
  let i2 : Fin (pair12Count S.D) := ⟨2, by omega⟩
  let c0 := pair12ExactReturn S hexact i0
  let c1 := pair12ExactReturn S hexact i1
  let c2 := pair12ExactReturn S hexact i2
  have hbound (i : Fin (pair12Count S.D)) : pair12ExactReturn S hexact i ≤ 2 := by
    have heq := pair12ExactBoundary_rho_axis_residual S hexact i
    have hm : Point3.mk 0 0 (pair12ExactReturn S hexact i) ∈ S.D := by
      rw [← heq]
      exact S.rho_mem _
    have hlt := (pure3_axis_mem_iff S _).mp hm
    omega
  have hb0 := hbound i0
  have hb1 := hbound i1
  have hb2 := hbound i2
  change c0 ≤ 2 at hb0
  change c1 ≤ 2 at hb1
  change c2 ≤ 2 at hb2
  have hne02 : c0 ≠ c2 := by
    intro h
    have hb := pair12ReturnCoord_injective S h
    have hx := congrArg (fun b : Pair12Boundary S => b.1.x) hb
    simp [c0, c2, i0, i2, pair12ExactReturn, pair12ExactBoundary] at hx
  have hgap01 : 2 ≤ c1 - c0 ∨ 2 ≤ c0 - c1 := by
    rcases lt_trichotomy c0 c1 with h | h | h
    · exact Or.inl (by
        simpa [c0, c1, i0, i1, ht] using
          pair12ExactReturn_step_up S hexact (i := 0) (by omega) h)
    · exact False.elim ((pair12ExactReturn_adjacent_ne S hexact (i := 0) (by omega)) h)
    · exact Or.inr (by
        simpa [c0, c1, i0, i1, hs] using
          pair12ExactReturn_step_down S hexact (i := 0) (by omega) h)
  have hgap12 : 2 ≤ c2 - c1 ∨ 2 ≤ c1 - c2 := by
    rcases lt_trichotomy c1 c2 with h | h | h
    · exact Or.inl (by
        simpa [c1, c2, i1, i2, ht] using
          pair12ExactReturn_step_up S hexact (i := 1) (by omega) h)
    · exact False.elim ((pair12ExactReturn_adjacent_ne S hexact (i := 1) (by omega)) h)
    · exact Or.inr (by
        simpa [c1, c2, i1, i2, hs] using
          pair12ExactReturn_step_down S hexact (i := 1) (by omega) h)
  omega

theorem noFull_residual_succ_s_2 (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (hsucc : pair12Count S.D = pair13Count S.D + 1)
    (htwo : pair23Count S.D = 2) : noFullTarget S ≤ S.m := by
  let s := pair13Count S.D
  have hs : 2 ≤ s := by have := hord.1; dsimp [s]; omega
  have hlt : pair13Count S.D < pair12Count S.D := by omega
  have hacc := strict_resource_accounting S hnf hord hlt
  have hcore := fullCore_card_lower_t2 S hlt htwo
  have harith := unbalanced_residual_succ_s_2 s hs
  have htarget : noFullTarget S = quarterSquareCeil ((s + 1) + s + 2 + 1) := by
    simp [noFullTarget, s, hsucc, htwo]
  have haccS : strictM5 (s + 1) s 2 + (fullCoreFinset S).card +
      strictResourceExcess S ≤ S.m := by
    simpa [strictM5, s, hsucc, htwo] using hacc
  have hcoreS : s - 1 ≤ (fullCoreFinset S).card := by simpa [s] using hcore
  rw [htarget]
  by_contra hfail
  have hres0 : strictResourceExcess S = 0 := by
    omega
  have hz := strictResourceExcess_summands_eq_zero S hres0
  have hnot12 : ¬ Pair12OriginFree S := by
    intro hof
    have hp := pair12_originFree_strict_resource S hof
    omega
  have htwoOF := two_pairFamilies_originFree S hnf
  have h13 : Pair13OriginFree S := by
    rcases htwoOF with h | h | h
    · exact False.elim (hnot12 h.1)
    · exact False.elim (hnot12 h.1)
    · exact h.1
  by_cases hs3 : 3 ≤ s
  · have hspan : pair12Count S.D - 1 < pair23Count S.D * (pair13Count S.D - 1) := by
      dsimp [s] at hs3
      rw [hsucc, htwo]
      omega
    have hp := pair13_originFree_strict_resource S (by omega) hspan h13
    omega
  · have hs2 : s = 2 := by omega
    have ha3 : pure3Intercept S = 3 := by
      have hz3 := hz.2.2.1
      unfold strictAxisExcess3 at hz3
      dsimp [s] at hs2
      have hr3 : pair12Count S.D = 3 := by omega
      have hle : pure3Intercept S ≤ pair12Count S.D := Nat.sub_eq_zero_iff_le.mp hz3
      have hge := strict_axis3_baseline S
      rw [hr3] at hle hge
      exact Nat.le_antisymm hle hge
    have hexact := pair12PlaneExact_of_extra_card_eq_zero S hz.2.2.2.1
    exact strict_residual_322_sequence_impossible S (by omega) (by omega) htwo ha3 hexact

theorem noFull_residual_433 (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (hr : pair12Count S.D = 4) (hs : pair13Count S.D = 3)
    (ht : pair23Count S.D = 3) : noFullTarget S ≤ S.m := by
  have hlt : pair13Count S.D < pair12Count S.D := by omega
  have hacc := strict_resource_accounting S hnf hord hlt
  have hcore := fullCore_card_lower_t3 S hord hlt ht
  have harith := unbalanced_residual_433
  have htarget : noFullTarget S = quarterSquareCeil (4 + 3 + 3 + 1) := by
    simp [noFullTarget, hr, hs, ht]
  have haccN : strictM5 4 3 3 + (fullCoreFinset S).card +
      strictResourceExcess S ≤ S.m := by
    simpa [strictM5, hr, hs, ht] using hacc
  have hcoreN : 5 ≤ (fullCoreFinset S).card := by
    rw [hs] at hcore
    norm_num at hcore ⊢
    exact hcore
  rw [htarget]
  by_contra hfail
  have hres : strictResourceExcess S ≤ 1 := by
    omega
  have hfamilies := two_pairFamilies_originFree S hnf
  have h12 (hof : Pair12OriginFree S) : 1 ≤ strictAxisExcess3 S :=
    pair12_originFree_strict_resource S hof
  have h13 (hof : Pair13OriginFree S) :
      1 ≤ strictAxisExcess2 S + (pair13ExtraFinset S).card := by
    apply pair13_originFree_strict_resource S (by omega) (by rw [hr, hs, ht]; norm_num) hof
  have h23 (hof : Pair23OriginFree S) :
      1 ≤ strictAxisExcess1 S + (pair23ExtraFinset S).card := by
    apply pair23_originFree_strict_resource S (by omega) (by rw [hr, hs, ht]; norm_num) hof
  unfold strictResourceExcess at hres
  rcases hfamilies with h | h | h
  · have := h12 h.1; have := h13 h.2; omega
  · have := h12 h.1; have := h23 h.2; omega
  · have := h13 h.1; have := h23 h.2; omega

theorem noFull_residual_543 (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (hr : pair12Count S.D = 5) (hs : pair13Count S.D = 4)
    (ht : pair23Count S.D = 3) : noFullTarget S ≤ S.m := by
  have hlt : pair13Count S.D < pair12Count S.D := by omega
  have hacc := strict_resource_accounting S hnf hord hlt
  have hcore := fullCore_card_lower_t3 S hord hlt ht
  have harith := unbalanced_residual_543
  have htarget : noFullTarget S = quarterSquareCeil (5 + 4 + 3 + 1) := by
    simp [noFullTarget, hr, hs, ht]
  have haccN : strictM5 5 4 3 + (fullCoreFinset S).card +
      strictResourceExcess S ≤ S.m := by
    simpa [strictM5, hr, hs, ht] using hacc
  have hcoreN : 8 ≤ (fullCoreFinset S).card := by
    rw [hs] at hcore
    norm_num at hcore ⊢
    exact hcore
  rw [htarget]
  by_contra hfail
  have hres0 : strictResourceExcess S = 0 := by
    omega
  have hz := strictResourceExcess_summands_eq_zero S hres0
  have hnot12 : ¬ Pair12OriginFree S := by
    intro hof
    have hp := pair12_originFree_strict_resource S hof
    omega
  have hfamilies := two_pairFamilies_originFree S hnf
  have h13 : Pair13OriginFree S := by
    rcases hfamilies with h | h | h
    · exact False.elim (hnot12 h.1)
    · exact False.elim (hnot12 h.1)
    · exact h.1
  have hp := pair13_originFree_strict_resource S (by omega)
    (by rw [hr, hs, ht]; norm_num) h13
  omega

end NSP3
