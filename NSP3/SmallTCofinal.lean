import NSP3.LargeTCofinal

namespace NSP3

private theorem t3_resource_budget (r s E : ℕ) (hs : 3 ≤ s) (hsr : s ≤ r)
    (hbudget :
      3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 + Nat.choose 3 2 +
          simplexCard s 3 + E ≤ quarterSquareCeil (r + s + 3 + 2))
    (hbudget_strict : s < r →
      3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 + Nat.choose 3 2 +
          (simplexCard s 3 + 1) + E ≤ quarterSquareCeil (r + s + 3 + 2)) :
    r - s ≤ 5 ∧ (r - s) + E ≤ 8 ∧ (r - s) + 2 * E ≤ 16 := by
  have hsimp := six_mul_simplexCard s 3 hs
  norm_num at hsimp
  have hsimp' : simplexCard s 3 = 3 * s - 5 := by omega
  rw [hsimp'] at hbudget
  have hid := fullDeficitIdentity r s 3
  norm_num at hid
  have hmz : ((r : ℤ) + s + 3) % 2 ≤ 1 := by omega
  have hbudgetz :
      (3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 + Nat.choose 3 2 +
          (3 * s - 5) + E : ℕ) ≤ quarterSquareCeil (r + s + 5) := by
    simpa [Nat.add_assoc] using hbudget
  have hbudgetz' :
      ((3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 + Nat.choose 3 2 +
          (3 * s - 5) + E : ℕ) : ℤ) ≤ (quarterSquareCeil (r + s + 5) : ℤ) := by
    exact_mod_cast hbudgetz
  have hquad : (4 : ℤ) * E + ((r : ℤ) - s) ^ 2 ≤ 32 := by
    push_cast at hbudgetz'
    rw [Nat.cast_sub (by omega : 5 ≤ 3 * s)] at hbudgetz'
    norm_num at hbudgetz'
    nlinarith
  have hxnonneg : (0 : ℤ) ≤ (r : ℤ) - s := by omega
  have hxle : r - s ≤ 5 := by
    have hxcast : ((r - s : ℕ) : ℤ) = (r : ℤ) - s := by
      rw [Nat.cast_sub hsr]
    nlinarith
  have hquad_strict (hrs : s < r) :
      (4 : ℤ) * E + ((r : ℤ) - s) ^ 2 ≤ 28 := by
    have hb := hbudget_strict hrs
    rw [hsimp'] at hb
    have hb' :
        ((3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 + Nat.choose 3 2 +
          ((3 * s - 5) + 1) + E : ℕ) : ℤ) ≤ (quarterSquareCeil (r + s + 5) : ℤ) := by
      exact_mod_cast hb
    push_cast at hb'
    rw [Nat.cast_sub (by omega : 5 ≤ 3 * s)] at hb'
    norm_num at hb'
    nlinarith
  refine ⟨hxle, ?_, ?_⟩
  · have hxcast : ((r - s : ℕ) : ℤ) = (r : ℤ) - s := by rw [Nat.cast_sub hsr]
    interval_cases h : r - s
    · rw [← hxcast] at hquad
      norm_num at hquad ⊢
      omega
    all_goals
      have hrs : s < r := by omega
      have hq := hquad_strict hrs
      rw [← hxcast] at hq
      norm_num at hq ⊢
      omega
  · have hxcast : ((r - s : ℕ) : ℤ) = (r : ℤ) - s := by rw [Nat.cast_sub hsr]
    interval_cases h : r - s
    · rw [← hxcast] at hquad
      norm_num at hquad ⊢
      omega
    all_goals
      have hrs : s < r := by omega
      have hq := hquad_strict hrs
      rw [← hxcast] at hq
      norm_num at hq ⊢
      omega

private theorem pair12BlockReturn_lower_t3 (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) (B : Pair12ExactBlock S)
    (j : Fin B.length) : 1 ≤ pair12BlockReturn S B j := by
  let i : Fin (pair12Count S.D) := ⟨B.start + j.1, by
    have := B.end_le
    omega⟩
  have hne := pair12_return_ne_zero_of_fullSupport S hg hfull
    (orderedPair12Boundary S i).2.1 (orderedPair12Boundary S i).2.2
  by_contra h
  have hz : pair12BlockReturn S B j = 0 := Nat.eq_zero_of_not_pos h
  apply hne
  apply Point3.ext
  · exact complementFaceReturn₁ S (orderedPair12Boundary S i).2.1
      (orderedPair12Boundary S i).2.2.1
  · exact complementFaceReturn₂ S (orderedPair12Boundary S i).2.1
      (orderedPair12Boundary S i).2.2.2.1
  · simpa [Point3.zero, pair12BlockReturn, orderedPair12Return,
      pair12ReturnCoord, i] using hz

private theorem pair13BlockReturn_lower_t3 (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) (B : Pair13ExactBlock S)
    (j : Fin B.length) : 1 ≤ pair13BlockReturn S B j := by
  let i : Fin (pair13Count S.D) := ⟨B.start + j.1, by
    have := B.end_le
    omega⟩
  have hne := pair13_return_ne_zero_of_fullSupport S hg hfull
    (orderedPair13Boundary S i).2.1 (orderedPair13Boundary S i).2.2
  by_contra h
  have hz : pair13BlockReturn S B j = 0 := Nat.eq_zero_of_not_pos h
  apply hne
  apply Point3.ext
  · exact complementFaceReturn₁ S (orderedPair13Boundary S i).2.1
      (orderedPair13Boundary S i).2.2.1
  · simpa [Point3.zero, pair13BlockReturn, orderedPair13Return,
      pair13ReturnCoord, i] using hz
  · exact complementFaceReturn₃ S (orderedPair13Boundary S i).2.1
      (orderedPair13Boundary S i).2.2.2.2

private theorem pair12BlockReturn_upper_t3 (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) (B : Pair12ExactBlock S)
    (j : Fin B.length) :
    pair12BlockReturn S B j ≤ pair12Count S.D + fullAxisExcess3 S := by
  let i : Fin (pair12Count S.D) := ⟨B.start + j.1, by
    have := B.end_le
    omega⟩
  have hrho : S.rho (orderedPair12Boundary S i).1 =
      Point3.mk 0 0 (pair12BlockReturn S B j) := by
    apply Point3.ext
    · exact complementFaceReturn₁ S (orderedPair12Boundary S i).2.1
        (orderedPair12Boundary S i).2.2.1
    · exact complementFaceReturn₂ S (orderedPair12Boundary S i).2.1
        (orderedPair12Boundary S i).2.2.2.1
    · rfl
  have hmem : Point3.mk 0 0 (pair12BlockReturn S B j) ∈ S.D := by
    rw [← hrho]
    exact S.rho_mem _
  have hlt := (pure3_axis_mem_iff S _).mp hmem
  have hcap := pair12_return_capacity_fullSupport S hg hfull
  unfold fullAxisExcess3
  omega

private theorem pair13BlockReturn_upper_t3 (S : CyclicStaircase) (B : Pair13ExactBlock S)
    (j : Fin B.length) :
    pair13BlockReturn S B j ≤ pair12Count S.D + fullAxisExcess2 S := by
  let i : Fin (pair13Count S.D) := ⟨B.start + j.1, by
    have := B.end_le
    omega⟩
  have hrho : S.rho (orderedPair13Boundary S i).1 =
      Point3.mk 0 (pair13BlockReturn S B j) 0 := by
    apply Point3.ext
    · exact complementFaceReturn₁ S (orderedPair13Boundary S i).2.1
        (orderedPair13Boundary S i).2.2.1
    · rfl
    · exact complementFaceReturn₃ S (orderedPair13Boundary S i).2.1
        (orderedPair13Boundary S i).2.2.2.2
  have hmem : Point3.mk 0 (pair13BlockReturn S B j) 0 ∈ S.D := by
    rw [← hrho]
    exact S.rho_mem _
  have hlt := (pure2_axis_mem_iff S _).mp hmem
  have hbase := pair12_intercept2_lower S
  unfold fullAxisExcess2
  omega

private theorem pair12BlockReturn_injective_t3 (S : CyclicStaircase)
    (B : Pair12ExactBlock S) : Function.Injective (pair12BlockReturn S B) := by
  intro a b hab
  have hb := pair12ReturnCoord_injective S hab
  have hx := congrArg (fun z : Pair12Boundary S => z.1.x) hb
  have hi := (orderedPair12Boundary_x_strictMono S).injective hx
  apply Fin.ext
  have hv := congrArg Fin.val hi
  simp at hv
  omega

private theorem pair13BlockReturn_injective_t3 (S : CyclicStaircase)
    (B : Pair13ExactBlock S) : Function.Injective (pair13BlockReturn S B) := by
  intro a b hab
  have hb := pair13ReturnCoord_injective S hab
  have hx := congrArg (fun z : Pair13Boundary S => z.1.x) hb
  have hi := (orderedPair13Boundary_x_strictMono S).injective hx
  apply Fin.ext
  have hv := congrArg Fin.val hi
  simp at hv
  omega

private theorem t3_pair12_block_mixed (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 3)
    (hr : 16 ≤ pair12Count S.D) {K : ℕ}
    (hgap : pair12Count S.D - pair13Count S.D ≤ 5)
    (hbudget1 : (pair12Count S.D - pair13Count S.D) + K ≤ 8)
    (hbudget : (pair12Count S.D - pair13Count S.D) + 2 * K ≤ 16)
    (hK : fullAxisExcess2 S + fullAxisExcess3 S +
      (pair12ExtraFinset S).card + (pair13ExtraFinset S).card ≤ K)
    (B : Pair12ExactBlock S) (hL : 2 ≤ B.length) :
    (∃ i : Fin (B.length - 1),
      pair12BlockReturn S B (edgeLeft i) < pair12BlockReturn S B (edgeRight i)) ∧
    (∃ i : Fin (B.length - 1),
      pair12BlockReturn S B (edgeRight i) < pair12BlockReturn S B (edgeLeft i)) := by
  let c := pair12BlockReturn S B
  have hlo : ∀ i, 1 ≤ c i := pair12BlockReturn_lower_t3 S hg hfull B
  have hhi : ∀ i, c i ≤ pair12Count S.D + fullAxisExcess3 S :=
    pair12BlockReturn_upper_t3 S hg hfull B
  have hinj : Function.Injective c := pair12BlockReturn_injective_t3 S B
  have hK8 : K ≤ 8 := by omega
  have heK : (pair12ExtraFinset S).card + fullAxisExcess3 S ≤ K := by omega
  constructor
  · by_contra hn
    have hstep : ∀ i : Fin (B.length - 1),
        c (edgeRight i) < c (edgeLeft i) ∧
        pair13Count S.D ≤ c (edgeLeft i) - c (edgeRight i) := by
      intro i
      have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
        intro heq
        have hi := hinj heq
        have hv := congrArg Fin.val hi
        simp [edgeLeft, edgeRight] at hv
      have hlt : c (edgeRight i) < c (edgeLeft i) := by
        by_contra hnot
        have : c (edgeLeft i) < c (edgeRight i) := by omega
        exact hn ⟨i, this⟩
      refine ⟨hlt, pair12LocalReturn_step_down S (by omega)
        (pair12BlockReturn_adjacent_residue S B i) hlt⟩
    have hspan := allNegativeEdgeSpan c hL hlo hhi hstep
    have hslo : pair12Count S.D - 5 ≤ pair13Count S.D := by omega
    have hlen : pair12Count S.D - 8 ≤ B.length := by
      have := B.length_lower
      omega
    have hmulle : (pair12Count S.D - 5) * (pair12Count S.D - 9) ≤
        pair13Count S.D * (B.length - 1) :=
      Nat.mul_le_mul hslo (by omega)
    have hsub5 : pair12Count S.D - 5 + 5 = pair12Count S.D := by omega
    have hsub9 : pair12Count S.D - 9 + 9 = pair12Count S.D := by omega
    have hpoly : pair12Count S.D + 7 <
        (pair12Count S.D - 5) * (pair12Count S.D - 9) := by
      nlinarith
    omega
  · by_contra hn
    have hstep : ∀ i : Fin (B.length - 1),
        c (edgeLeft i) < c (edgeRight i) ∧
        pair23Count S.D ≤ c (edgeRight i) - c (edgeLeft i) := by
      intro i
      have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
        intro heq
        have hi := hinj heq
        have hv := congrArg Fin.val hi
        simp [edgeLeft, edgeRight] at hv
      have hlt : c (edgeLeft i) < c (edgeRight i) := by
        by_contra hnot
        have : c (edgeRight i) < c (edgeLeft i) := by omega
        exact hn ⟨i, this⟩
      refine ⟨hlt, pair12LocalReturn_step_up S (by omega)
        (pair12BlockReturn_adjacent_residue S B i) hlt⟩
    have hspan := allPositiveEdgeSpan c hL hlo hhi hstep
    have hlen := B.length_lower
    rw [ht] at hspan
    omega

private theorem t3_pair13_block_mixed (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 3)
    (hr : 16 ≤ pair12Count S.D) {K : ℕ}
    (hgap : pair12Count S.D - pair13Count S.D ≤ 5)
    (hbudget1 : (pair12Count S.D - pair13Count S.D) + K ≤ 8)
    (hbudget : (pair12Count S.D - pair13Count S.D) + 2 * K ≤ 16)
    (hK : fullAxisExcess2 S + fullAxisExcess3 S +
      (pair12ExtraFinset S).card + (pair13ExtraFinset S).card ≤ K)
    (B : Pair13ExactBlock S) (hL : 2 ≤ B.length) :
    (∃ i : Fin (B.length - 1),
      pair13BlockReturn S B (edgeLeft i) < pair13BlockReturn S B (edgeRight i)) ∧
    (∃ i : Fin (B.length - 1),
      pair13BlockReturn S B (edgeRight i) < pair13BlockReturn S B (edgeLeft i)) := by
  let c := pair13BlockReturn S B
  have hlo : ∀ i, 1 ≤ c i := pair13BlockReturn_lower_t3 S hg hfull B
  have hhi : ∀ i, c i ≤ pair12Count S.D + fullAxisExcess2 S :=
    pair13BlockReturn_upper_t3 S B
  have hinj : Function.Injective c := pair13BlockReturn_injective_t3 S B
  have hK8 : K ≤ 8 := by omega
  have heK : (pair13ExtraFinset S).card + fullAxisExcess2 S ≤ K := by omega
  constructor
  · by_contra hn
    have hstep : ∀ i : Fin (B.length - 1),
        c (edgeRight i) < c (edgeLeft i) ∧
        pair12Count S.D ≤ c (edgeLeft i) - c (edgeRight i) := by
      intro i
      have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
        intro heq
        have hi := hinj heq
        have hv := congrArg Fin.val hi
        simp [edgeLeft, edgeRight] at hv
      have hlt : c (edgeRight i) < c (edgeLeft i) := by
        by_contra hnot
        have : c (edgeLeft i) < c (edgeRight i) := by omega
        exact hn ⟨i, this⟩
      refine ⟨hlt, pair13LocalReturn_step_down S (by omega)
        (pair13BlockReturn_adjacent_residue S B i) hlt⟩
    have hspan := allNegativeEdgeSpan c hL hlo hhi hstep
    have hslo : pair12Count S.D - 5 ≤ pair13Count S.D := by omega
    have hlen : pair12Count S.D - 13 ≤ B.length := by
      have := B.length_lower
      omega
    have hmulle : pair12Count S.D * (pair12Count S.D - 14) ≤
        pair12Count S.D * (B.length - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hsub14 : pair12Count S.D - 14 + 14 = pair12Count S.D := by omega
    have hpoly : pair12Count S.D + 7 <
        pair12Count S.D * (pair12Count S.D - 14) := by
      nlinarith
    omega
  · by_contra hn
    have hstep : ∀ i : Fin (B.length - 1),
        c (edgeLeft i) < c (edgeRight i) ∧
        pair23Count S.D ≤ c (edgeRight i) - c (edgeLeft i) := by
      intro i
      have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
        intro heq
        have hi := hinj heq
        have hv := congrArg Fin.val hi
        simp [edgeLeft, edgeRight] at hv
      have hlt : c (edgeLeft i) < c (edgeRight i) := by
        by_contra hnot
        have : c (edgeRight i) < c (edgeLeft i) := by omega
        exact hn ⟨i, this⟩
      refine ⟨hlt, pair13LocalReturn_step_up S (by omega)
        (pair13BlockReturn_adjacent_residue S B i) hlt⟩
    have hspan := allPositiveEdgeSpan c hL hlo hhi hstep
    have hlen := B.length_lower
    rw [ht] at hspan
    omega

/-- Cofinal closure of the ordered full-support branch at `t = 3`. -/
theorem fullSupport_t3_cofinal_strict (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 3)
    (hr : 16 ≤ pair12Count S.D) : fullTarget S < S.m := by
  classical
  by_contra hnot
  have hmle : S.m ≤ fullTarget S := by omega
  have hhole := coreHoleFinset_eq_empty_of_pair23_le_three S hg hfull hord (by omega)
  have hpart := card_fullCore_partition S g
  rw [hhole] at hpart
  simp at hpart
  have hs : 3 ≤ pair13Count S.D := by
    have := hord.1
    omega
  have hsimpP := simplexCard_le_punctured_add_hole S g hord
  rw [hhole] at hsimpP
  simp at hsimpP
  have hsimpP3 : simplexCard (pair13Count S.D) 3 ≤
      (orderedSimplexPunctured S g).card := by
    simpa [ht] using hsimpP
  have horderedSub : orderedSimplexPunctured S g ⊆ puncturedFullCoreFinset S g := by
    intro p hp
    have hpf := Finset.mem_filter.mp hp
    rw [mem_puncturedFullCoreFinset]
    constructor
    · rcases Finset.mem_image.mp hpf.1 with ⟨i, _hi, rfl⟩
      exact orderedSimplex_fullCore S hord i
    · exact hpf.2
  have horderedCard : (orderedSimplexPunctured S g).card ≤
      (puncturedFullCoreFinset S g).card := Finset.card_le_card horderedSub
  have haccount := full_resource_accounting S hg hfull
  have haccount' :
      3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
          Nat.choose (pair13Count S.D) 2 + Nat.choose 3 2 +
          (puncturedFullCoreFinset S g).card + fullResourceExcess S ≤ S.m := by
    simpa [fullM, ht] using haccount
  have hbase :
      3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
          Nat.choose (pair13Count S.D) 2 + Nat.choose 3 2 +
          simplexCard (pair13Count S.D) 3 + fullResourceExcess S ≤
        fullTarget S := by
    omega
  have hstrict : pair13Count S.D < pair12Count S.D →
      3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
          Nat.choose (pair13Count S.D) 2 + Nat.choose 3 2 +
          (simplexCard (pair13Count S.D) 3 + 1) + fullResourceExcess S ≤
        fullTarget S := by
    intro hrs
    have hcore := fullCore_card_lower_t3 S hord hrs ht
    have hsimp := six_mul_simplexCard (pair13Count S.D) 3 hs
    norm_num at hsimp
    have hsimp' : simplexCard (pair13Count S.D) 3 = 3 * pair13Count S.D - 5 := by
      omega
    have hplus : simplexCard (pair13Count S.D) 3 + 1 ≤
        (puncturedFullCoreFinset S g).card := by
      rw [hsimp', ← hpart]
      omega
    unfold fullM at haccount
    rw [ht] at haccount
    omega
  have hbase' :
      3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
          Nat.choose (pair13Count S.D) 2 + Nat.choose 3 2 +
          simplexCard (pair13Count S.D) 3 + fullResourceExcess S ≤
        quarterSquareCeil (pair12Count S.D + pair13Count S.D + 3 + 2) := by
    simpa [fullTarget, ht] using hbase
  have hstrict' : pair13Count S.D < pair12Count S.D →
      3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
          Nat.choose (pair13Count S.D) 2 + Nat.choose 3 2 +
          (simplexCard (pair13Count S.D) 3 + 1) + fullResourceExcess S ≤
        quarterSquareCeil (pair12Count S.D + pair13Count S.D + 3 + 2) := by
    intro hrs
    simpa [fullTarget, ht] using hstrict hrs
  have hbud := t3_resource_budget (pair12Count S.D) (pair13Count S.D)
    (fullResourceExcess S) hs hord.2 hbase' hstrict'
  let K := fullAxisExcess2 S + fullAxisExcess3 S +
    (pair12ExtraFinset S).card + (pair13ExtraFinset S).card
  have hK : K ≤ fullResourceExcess S := by
    dsimp [K]
    unfold fullResourceExcess
    omega
  have hgap : pair12Count S.D - pair13Count S.D ≤ 5 := hbud.1
  have hbudget1 : (pair12Count S.D - pair13Count S.D) + K ≤ 8 := by omega
  have hbudget2 : (pair12Count S.D - pair13Count S.D) + 2 * K ≤ 16 := by omega
  have hKdata : fullAxisExcess2 S + fullAxisExcess3 S +
      (pair12ExtraFinset S).card + (pair13ExtraFinset S).card ≤ K := by rfl
  have he12 : (pair12ExtraFinset S).card < pair12Count S.D := by
    dsimp [K] at hbudget1
    omega
  have he13 : (pair13ExtraFinset S).card < pair13Count S.D := by
    dsimp [K] at hbudget1
    omega
  let B12 := pair12ExactBlock S he12
  let B13 := pair13ExactBlock S he13
  have hL12 : 2 ≤ B12.length := by
    have hlen := B12.length_lower
    dsimp [K] at hbudget1
    omega
  have hL13 : 2 ≤ B13.length := by
    have hlen := B13.length_lower
    dsimp [K] at hbudget1
    omega
  have hmixed12 := t3_pair12_block_mixed S hg hfull hord ht hr hgap
    hbudget1 hbudget2 hKdata B12 hL12
  have hmixed13 := t3_pair13_block_mixed S hg hfull hord ht hr hgap
    hbudget1 hbudget2 hKdata B13 hL13
  exact fullSupport_mixedExactBlocks_impossible S hg hfull hord B12 B13 hL12 hL13
    (by omega) (by omega) hmixed12.1 hmixed12.2 hmixed13.1 hmixed13.2
    hKdata (by omega)

private theorem target_le_baseline_t0 (r s : ℕ) (hsr : s ≤ r) :
    quarterSquareCeil (r + s + 0 + 2) ≤
      3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 + Nat.choose 0 2 := by
  have hid := fullDeficitIdentity r s 0
  norm_num at hid
  norm_num only [Nat.choose_zero_right, add_zero] at ⊢
  by_cases hrs : r = s
  · subst s
    have hmod : ((r : ℤ) + r) % 2 = 0 := by omega
    rw [hmod] at hid
    norm_num at hid
    exact_mod_cast (show (quarterSquareCeil (r + r + 2) : ℤ) ≤
      (3 * r + 1 + Nat.choose r 2 + Nat.choose r 2 : ℕ) by omega)
  · have hgap : (4 : ℤ) ≤ (r : ℤ) - s + 3 := by
      have : s < r := by omega
      exact_mod_cast (show 4 ≤ r - s + 3 by omega)
    have hsq : (16 : ℤ) ≤ ((r : ℤ) - s + 3) ^ 2 := by nlinarith
    have hmz : ((r : ℤ) + s) % 2 ≤ 1 := by omega
    have hz : (quarterSquareCeil (r + s + 2) : ℤ) ≤
        (3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 : ℕ) := by
      omega
    exact_mod_cast hz

/-- The `t = 0` full-support branch is always strict. -/
theorem fullSupport_t0_strict (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 0) :
    fullTarget S < S.m := by
  let p := Point3.mk 0 1 1
  have hple : p ≤ g := by
    exact ⟨Nat.zero_le _, hfull.2.1, hfull.2.2⟩
  have hpne : p ≠ g := by
    intro heq
    have hx := congrArg Point3.x heq
    have hgx := hfull.1
    dsimp [p] at hx
    omega
  have hpbox : p ∈ lowerBoxFinset g := (mem_lowerBoxFinset g p).mpr ⟨hple, hpne⟩
  have hpD : p ∈ S.D := lowerBoxFinset_subset_D hg hpbox
  have hpextra : p ∈ pair23ExtraFinset S := by
    apply (mem_pair23ExtraFinset S p).mpr
    simp [p, hpD, ht]
  have hextra : 1 ≤ (pair23ExtraFinset S).card := by
    exact Finset.one_le_card.mpr ⟨p, hpextra⟩
  have haccount := full_resource_accounting S hg hfull
  have hM : fullM S + 1 ≤ S.m := by
    unfold fullResourceExcess at haccount
    omega
  have htarget : fullTarget S ≤ fullM S := by
    unfold fullTarget fullM
    rw [ht]
    apply target_le_baseline_t0
    exact hord.2
  omega

/-- A hypothetical `t = 3` counterexample satisfies the gap condition used by
the frozen residual predicate. -/
theorem fullSupport_t3_gap_le_five_of_counterexample (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 3)
    (hcounter : S.m ≤ fullTarget S) :
    pair12Count S.D ≤ pair13Count S.D + 5 := by
  classical
  have hhole := coreHoleFinset_eq_empty_of_pair23_le_three S hg hfull hord (by omega)
  have hpart := card_fullCore_partition S g
  rw [hhole] at hpart
  simp at hpart
  have hs : 3 ≤ pair13Count S.D := by
    have := hord.1
    omega
  have hsimpP := simplexCard_le_punctured_add_hole S g hord
  rw [hhole] at hsimpP
  simp at hsimpP
  have hsimpP3 : simplexCard (pair13Count S.D) 3 ≤
      (orderedSimplexPunctured S g).card := by
    simpa [ht] using hsimpP
  have horderedSub : orderedSimplexPunctured S g ⊆ puncturedFullCoreFinset S g := by
    intro p hp
    have hpf := Finset.mem_filter.mp hp
    rw [mem_puncturedFullCoreFinset]
    constructor
    · rcases Finset.mem_image.mp hpf.1 with ⟨i, _hi, rfl⟩
      exact orderedSimplex_fullCore S hord i
    · exact hpf.2
  have horderedCard : (orderedSimplexPunctured S g).card ≤
      (puncturedFullCoreFinset S g).card := Finset.card_le_card horderedSub
  have haccount := full_resource_accounting S hg hfull
  have haccount' :
      3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
          Nat.choose (pair13Count S.D) 2 + Nat.choose 3 2 +
          (puncturedFullCoreFinset S g).card + fullResourceExcess S ≤ S.m := by
    simpa [fullM, ht] using haccount
  have hbase :
      3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
          Nat.choose (pair13Count S.D) 2 + Nat.choose 3 2 +
          simplexCard (pair13Count S.D) 3 + fullResourceExcess S ≤
        fullTarget S := by
    omega
  have hstrict : pair13Count S.D < pair12Count S.D →
      3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
          Nat.choose (pair13Count S.D) 2 + Nat.choose 3 2 +
          (simplexCard (pair13Count S.D) 3 + 1) + fullResourceExcess S ≤
        fullTarget S := by
    intro hrs
    have hcore := fullCore_card_lower_t3 S hord hrs ht
    have hsimp := six_mul_simplexCard (pair13Count S.D) 3 hs
    norm_num at hsimp
    have hsimp' : simplexCard (pair13Count S.D) 3 = 3 * pair13Count S.D - 5 := by
      omega
    have hplus : simplexCard (pair13Count S.D) 3 + 1 ≤
        (puncturedFullCoreFinset S g).card := by
      rw [hsimp', ← hpart]
      omega
    unfold fullM at haccount
    rw [ht] at haccount
    omega
  have hbase' :
      3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
          Nat.choose (pair13Count S.D) 2 + Nat.choose 3 2 +
          simplexCard (pair13Count S.D) 3 + fullResourceExcess S ≤
        quarterSquareCeil (pair12Count S.D + pair13Count S.D + 3 + 2) := by
    simpa [fullTarget, ht] using hbase
  have hstrict' : pair13Count S.D < pair12Count S.D →
      3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
          Nat.choose (pair13Count S.D) 2 + Nat.choose 3 2 +
          (simplexCard (pair13Count S.D) 3 + 1) + fullResourceExcess S ≤
        quarterSquareCeil (pair12Count S.D + pair13Count S.D + 3 + 2) := by
    intro hrs
    simpa [fullTarget, ht] using hstrict hrs
  have hbud := t3_resource_budget (pair12Count S.D) (pair13Count S.D)
    (fullResourceExcess S) hs hord.2 hbase' hstrict'
  omega

private theorem t2_resource_budget (r s E : ℕ) (hs : 2 ≤ s) (hsr : s ≤ r)
    (hbudget :
      3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 + Nat.choose 2 2 +
          (s - 1) + E ≤ quarterSquareCeil (r + s + 2 + 2)) :
    E ≤ s + 3 ∧ 4 * E + (r - s + 1) ^ 2 ≤ 4 * s + 16 := by
  have hid := fullDeficitIdentity r s 2
  norm_num at hid
  have hbz :
      ((3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 + Nat.choose 2 2 +
          (s - 1) + E : ℕ) : ℤ) ≤ (quarterSquareCeil (r + s + 4) : ℤ) := by
    exact_mod_cast hbudget
  push_cast at hbz
  rw [Nat.cast_sub (by omega : 1 ≤ s)] at hbz
  norm_num at hbz
  have hmod : ((r + s) % 2 : ℕ) ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hmodz : (((r + s) % 2 : ℕ) : ℤ) ≤ 1 := by exact_mod_cast hmod
  have hx : (1 : ℤ) ≤ (r : ℤ) - s + 1 := by exact_mod_cast (show 1 ≤ r - s + 1 by omega)
  have hsq : (1 : ℤ) ≤ ((r : ℤ) - s + 1) ^ 2 := by nlinarith
  have hquad : (4 : ℤ) * E + ((r : ℤ) - s + 1) ^ 2 ≤ 4 * s + 16 := by
    nlinarith
  constructor
  · nlinarith
  · have hcast : (((r - s + 1 : ℕ) : ℤ)) = (r : ℤ) - s + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hsr]
      norm_num
    exact_mod_cast hquad

private theorem t1_resource_budget (r s E : ℕ) (hsr : s ≤ r)
    (hbudget :
      3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 + Nat.choose 1 2 + E ≤
        quarterSquareCeil (r + s + 1 + 2)) :
    E ≤ s + 2 := by
  have hid := fullDeficitIdentity r s 1
  norm_num at hid
  have hbz :
      ((3 * r + 1 + Nat.choose r 2 + Nat.choose s 2 + Nat.choose 1 2 + E : ℕ) : ℤ) ≤
        (quarterSquareCeil (r + s + 3) : ℤ) := by
    exact_mod_cast hbudget
  push_cast at hbz
  norm_num at hbz
  have hmod : ((r + s + 1) % 2 : ℕ) ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hmodz : (((r + s + 1) % 2 : ℕ) : ℤ) ≤ 1 := by exact_mod_cast hmod
  have hx : (2 : ℤ) ≤ (r : ℤ) - s + 2 := by exact_mod_cast (show 2 ≤ r - s + 2 by omega)
  have hsq : (4 : ℤ) ≤ ((r : ℤ) - s + 2) ^ 2 := by nlinarith
  nlinarith

private theorem lowerBox_x_arm_card (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (ht : pair23Count S.D = 2) (hyz : 3 ≤ g.y + g.z) :
    g.x - 1 ≤ (lowerBoxFullOutsideCoreFinset S g).card := by
  classical
  let f : Fin (g.x - 1) → {p : Point3 // p ∈ lowerBoxFullOutsideCoreFinset S g} :=
    fun i => ⟨Point3.mk (i.1 + 1) g.y g.z, by
      rw [mem_lowerBoxFullOutsideCoreFinset]
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_⟩, ?_⟩
      · change i.1 + 1 ≤ g.x
        omega
      · rfl
      · rfl
      · intro heq
        have hx := congrArg Point3.x heq
        simp at hx
        omega
      · change 0 < i.1 + 1
        omega
      · exact hfull.2.1
      · exact hfull.2.2
      · intro hcore
        unfold FullCore at hcore
        rw [ht] at hcore
        simp only [Point3.x, Point3.y, Point3.z] at hcore
        omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hx := congrArg (fun p : {p : Point3 // p ∈ lowerBoxFullOutsideCoreFinset S g} => p.1.x) hij
    simpa [f] using hx
  have hc := Fintype.card_le_of_injective f hf
  simpa [f] using hc

private theorem pair23_lowerBox_arms_card (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (ht : pair23Count S.D = 2) :
    (g.y - 1) + (g.z - 1) ≤ (pair23ExtraFinset S).card := by
  classical
  let A := Fin (g.y - 1) ⊕ Fin (g.z - 1)
  let f : A → {p : Point3 // p ∈ pair23ExtraFinset S}
    | Sum.inl i => ⟨Point3.mk 0 (i.1 + 2) 1, by
        apply (mem_pair23ExtraFinset S _).mpr
        have hpbox : Point3.mk 0 (i.1 + 2) 1 ∈ lowerBoxFinset g := by
          rw [mem_lowerBoxFinset]
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          · change 0 ≤ g.x
            omega
          · change i.1 + 2 ≤ g.y
            omega
          · change 1 ≤ g.z
            exact hfull.2.2
          intro heq
          have hx := congrArg Point3.x heq
          simp at hx
          exact (Nat.ne_of_gt hfull.1) hx.symm
        exact ⟨lowerBoxFinset_subset_D hg hpbox, rfl, by norm_num, by norm_num, by
          simp only [Point3.y, Point3.z]
          omega⟩⟩
    | Sum.inr i => ⟨Point3.mk 0 1 (i.1 + 2), by
        apply (mem_pair23ExtraFinset S _).mpr
        have hpbox : Point3.mk 0 1 (i.1 + 2) ∈ lowerBoxFinset g := by
          rw [mem_lowerBoxFinset]
          refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
          · change 0 ≤ g.x
            omega
          · change 1 ≤ g.y
            exact hfull.2.1
          · change i.1 + 2 ≤ g.z
            omega
          intro heq
          have hx := congrArg Point3.x heq
          simp at hx
          exact (Nat.ne_of_gt hfull.1) hx.symm
        exact ⟨lowerBoxFinset_subset_D hg hpbox, rfl, by norm_num, by norm_num, by
          simp only [Point3.y, Point3.z]
          omega⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    rcases a with i | i <;> rcases b with j | j
    · apply congrArg Sum.inl
      apply Fin.ext
      have hy := congrArg (fun p : {p : Point3 // p ∈ pair23ExtraFinset S} => p.1.y) hab
      simpa [f] using hy
    · have hy := congrArg (fun p : {p : Point3 // p ∈ pair23ExtraFinset S} => p.1.y) hab
      have hz := congrArg (fun p : {p : Point3 // p ∈ pair23ExtraFinset S} => p.1.z) hab
      simp [f] at hy
    · have hy := congrArg (fun p : {p : Point3 // p ∈ pair23ExtraFinset S} => p.1.y) hab
      have hz := congrArg (fun p : {p : Point3 // p ∈ pair23ExtraFinset S} => p.1.z) hab
      simp [f] at hy
    · apply congrArg Sum.inr
      apply Fin.ext
      have hz := congrArg (fun p : {p : Point3 // p ∈ pair23ExtraFinset S} => p.1.z) hab
      simpa [f] using hz
  have hc := Fintype.card_le_of_injective f hf
  simpa [A, f] using hc

private theorem t1_lowerBox_card (S : CyclicStaircase) {g : Point3}
    (hfull : FullSupport g) (ht : pair23Count S.D = 1) :
    g.x * g.y * g.z - 1 ≤ (lowerBoxFullOutsideCoreFinset S g).card := by
  classical
  have hxpos : 0 < g.x := hfull.1
  have hypos : 0 < g.y := hfull.2.1
  have hzpos : 0 < g.z := hfull.2.2
  have hxlt : g.x - 1 < g.x := by omega
  have hylt : g.y - 1 < g.y := by omega
  have hzlt : g.z - 1 < g.z := by omega
  let triples := (Finset.range g.x).product
    ((Finset.range g.y).product (Finset.range g.z))
  let point : ℕ × (ℕ × ℕ) → Point3 := fun a => Point3.mk (a.1 + 1) (a.2.1 + 1) (a.2.2 + 1)
  let points := triples.image point
  have hinj : Set.InjOn point triples := by
    intro a ha b hb hab
    apply Prod.ext
    · have hx := congrArg Point3.x hab
      simpa [point] using hx
    · apply Prod.ext
      · have hy := congrArg Point3.y hab
        simpa [point] using hy
      · have hz := congrArg Point3.z hab
        simpa [point] using hz
  have hgmem : g ∈ points := by
    apply Finset.mem_image.mpr
    refine ⟨(g.x - 1, (g.y - 1, g.z - 1)), ?_, ?_⟩
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_range.mpr hxlt, Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr hylt, Finset.mem_range.mpr hzlt⟩⟩
    · apply Point3.ext <;> simp [point] <;> omega
  have hcard : (points.erase g).card = g.x * g.y * g.z - 1 := by
    rw [Finset.card_erase_of_mem hgmem]
    unfold points
    rw [Finset.card_image_iff.mpr hinj]
    simp [triples, Nat.mul_assoc]
  have hsub : points.erase g ⊆ lowerBoxFullOutsideCoreFinset S g := by
    intro p hp
    have hdata := Finset.mem_erase.mp hp
    rcases Finset.mem_image.mp hdata.2 with ⟨a, ha, rfl⟩
    have ha' := Finset.mem_product.mp ha
    have hab := Finset.mem_product.mp ha'.2
    simp only [Finset.mem_range] at ha' hab
    rw [mem_lowerBoxFullOutsideCoreFinset]
    refine ⟨⟨by simp [point]; omega, by simp [point]; omega, by simp [point]; omega⟩,
      ?_, ⟨by simp [point], by simp [point], by simp [point]⟩, ?_⟩
    · exact fun heq => hdata.1 (heq ▸ rfl)
    · intro hcore
      unfold FullCore at hcore
      rw [ht] at hcore
      simp [point] at hcore
      omega
  rw [← hcard]
  exact Finset.card_le_card hsub

private theorem t1_pair23_rectangle_card (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (ht : pair23Count S.D = 1) :
    g.y * g.z ≤ (pair23ExtraFinset S).card := by
  classical
  have hxpos : 0 < g.x := hfull.1
  have hypos : 0 < g.y := hfull.2.1
  have hzpos : 0 < g.z := hfull.2.2
  let pairs := (Finset.range g.y).product (Finset.range g.z)
  let point : ℕ × ℕ → Point3 := fun a => Point3.mk 0 (a.1 + 1) (a.2 + 1)
  let points := pairs.image point
  have hinj : Set.InjOn point pairs := by
    intro a ha b hb hab
    apply Prod.ext
    · have hy := congrArg Point3.y hab
      simpa [point] using hy
    · have hz := congrArg Point3.z hab
      simpa [point] using hz
  have hcard : points.card = g.y * g.z := by
    unfold points
    rw [Finset.card_image_iff.mpr hinj]
    simp [pairs]
  have hsub : points ⊆ pair23ExtraFinset S := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
    have ha' := Finset.mem_product.mp ha
    simp only [Finset.mem_range] at ha'
    apply (mem_pair23ExtraFinset S _).mpr
    have hpbox : Point3.mk 0 (a.1 + 1) (a.2 + 1) ∈ lowerBoxFinset g := by
      rw [mem_lowerBoxFinset]
      refine ⟨⟨by simp, by simp [point]; omega, by simp [point]; omega⟩, ?_⟩
      intro heq
      have hx := congrArg Point3.x heq
      simp at hx
      exact (Nat.ne_of_gt hfull.1) hx.symm
    refine ⟨lowerBoxFinset_subset_D hg hpbox, ?_, ?_, ?_, ?_⟩
    · change (Point3.mk 0 (a.1 + 1) (a.2 + 1)).x = 0
      rfl
    · change 0 < (Point3.mk 0 (a.1 + 1) (a.2 + 1)).y
      simp
    · change 0 < (Point3.mk 0 (a.1 + 1) (a.2 + 1)).z
      simp
    · change pair23Count S.D <
        (Point3.mk 0 (a.1 + 1) (a.2 + 1)).y +
          (Point3.mk 0 (a.1 + 1) (a.2 + 1)).z
      simp only [Point3.y, Point3.z]
      omega
  rw [← hcard]
  exact Finset.card_le_card hsub

private theorem pair12_thin_extra_card (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hr : 0 < pair12Count S.D) (hu : pair12Count S.D ≤ g.x) :
    g.x - pair12Count S.D + 1 ≤ (pair12ExtraFinset S).card := by
  classical
  have hypos : 0 < g.y := hfull.2.1
  have hzpos : 0 < g.z := hfull.2.2
  let f : Fin (g.x - pair12Count S.D + 1) → {p : Point3 // p ∈ pair12ExtraFinset S} :=
    fun i => ⟨Point3.mk (pair12Count S.D + i.1) 1 0, by
      apply (mem_pair12ExtraFinset S _).mpr
      have hpbox : Point3.mk (pair12Count S.D + i.1) 1 0 ∈ lowerBoxFinset g := by
        rw [mem_lowerBoxFinset]
        refine ⟨⟨by simp; omega, by simp; omega, by simp⟩, ?_⟩
        intro heq
        have hz := congrArg Point3.z heq
        simp at hz
        exact (Nat.ne_of_gt hfull.2.2) hz.symm
      exact ⟨lowerBoxFinset_subset_D hg hpbox, by simp; omega, by norm_num, rfl,
        by simp only [Point3.x, Point3.y]; omega⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hx := congrArg (fun p : {p : Point3 // p ∈ pair12ExtraFinset S} => p.1.x) hij
    simpa [f] using hx
  have hc := Fintype.card_le_of_injective f hf
  simpa [f] using hc

private theorem pair13_thin_extra_card (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hs : 0 < pair13Count S.D) (hu : pair13Count S.D ≤ g.x) :
    g.x - pair13Count S.D + 1 ≤ (pair13ExtraFinset S).card := by
  classical
  have hypos : 0 < g.y := hfull.2.1
  have hzpos : 0 < g.z := hfull.2.2
  let f : Fin (g.x - pair13Count S.D + 1) → {p : Point3 // p ∈ pair13ExtraFinset S} :=
    fun i => ⟨Point3.mk (pair13Count S.D + i.1) 0 1, by
      apply (mem_pair13ExtraFinset S _).mpr
      have hpbox : Point3.mk (pair13Count S.D + i.1) 0 1 ∈ lowerBoxFinset g := by
        rw [mem_lowerBoxFinset]
        refine ⟨⟨by simp; omega, by simp, by simp; omega⟩, ?_⟩
        intro heq
        have hy := congrArg Point3.y heq
        simp at hy
        exact (Nat.ne_of_gt hfull.2.1) hy.symm
      exact ⟨lowerBoxFinset_subset_D hg hpbox, by simp; omega, rfl, by norm_num,
        by simp only [Point3.x, Point3.z]; omega⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hx := congrArg (fun p : {p : Point3 // p ∈ pair13ExtraFinset S} => p.1.x) hij
    simpa [f] using hx
  have hc := Fintype.card_le_of_injective f hf
  simpa [f] using hc

private theorem t2_pair12_block_mixed (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 2)
    (hr : 10 ≤ pair12Count S.D) {K : ℕ}
    (hbudget1 : (pair12Count S.D - pair13Count S.D) + K ≤ 4)
    (hK : fullAxisExcess2 S + fullAxisExcess3 S +
      (pair12ExtraFinset S).card + (pair13ExtraFinset S).card ≤ K)
    (B : Pair12ExactBlock S) (hL : 2 ≤ B.length) :
    (∃ i : Fin (B.length - 1),
      pair12BlockReturn S B (edgeLeft i) < pair12BlockReturn S B (edgeRight i)) ∧
    (∃ i : Fin (B.length - 1),
      pair12BlockReturn S B (edgeRight i) < pair12BlockReturn S B (edgeLeft i)) := by
  let c := pair12BlockReturn S B
  have hlo : ∀ i, 1 ≤ c i := pair12BlockReturn_lower_t3 S hg hfull B
  have hhi : ∀ i, c i ≤ pair12Count S.D + fullAxisExcess3 S :=
    pair12BlockReturn_upper_t3 S hg hfull B
  have hinj : Function.Injective c := pair12BlockReturn_injective_t3 S B
  have hK4 : K ≤ 4 := by omega
  have heK : (pair12ExtraFinset S).card + fullAxisExcess3 S ≤ K := by omega
  constructor
  · by_contra hn
    have hstep : ∀ i : Fin (B.length - 1),
        c (edgeRight i) < c (edgeLeft i) ∧
        pair13Count S.D ≤ c (edgeLeft i) - c (edgeRight i) := by
      intro i
      have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
        intro heq
        have hi := hinj heq
        have hv := congrArg Fin.val hi
        simp [edgeLeft, edgeRight] at hv
      have hlt : c (edgeRight i) < c (edgeLeft i) := by
        by_contra hnot
        have : c (edgeLeft i) < c (edgeRight i) := by omega
        exact hn ⟨i, this⟩
      exact ⟨hlt, pair12LocalReturn_step_down S (by omega)
        (pair12BlockReturn_adjacent_residue S B i) hlt⟩
    have hspan := allNegativeEdgeSpan c hL hlo hhi hstep
    have hslo : pair12Count S.D - 4 ≤ pair13Count S.D := by omega
    have hlen : pair12Count S.D - 4 ≤ B.length := by
      have := B.length_lower
      omega
    have hmulle : (pair12Count S.D - 4) * (pair12Count S.D - 5) ≤
        pair13Count S.D * (B.length - 1) := Nat.mul_le_mul hslo (by omega)
    have hsub4 : pair12Count S.D - 4 + 4 = pair12Count S.D := by omega
    have hsub5 : pair12Count S.D - 5 + 5 = pair12Count S.D := by omega
    have hpoly : pair12Count S.D + 3 <
        (pair12Count S.D - 4) * (pair12Count S.D - 5) := by nlinarith
    omega
  · by_contra hn
    have hstep : ∀ i : Fin (B.length - 1),
        c (edgeLeft i) < c (edgeRight i) ∧
        pair23Count S.D ≤ c (edgeRight i) - c (edgeLeft i) := by
      intro i
      have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
        intro heq
        have hi := hinj heq
        have hv := congrArg Fin.val hi
        simp [edgeLeft, edgeRight] at hv
      have hlt : c (edgeLeft i) < c (edgeRight i) := by
        by_contra hnot
        have : c (edgeRight i) < c (edgeLeft i) := by omega
        exact hn ⟨i, this⟩
      exact ⟨hlt, pair12LocalReturn_step_up S (by omega)
        (pair12BlockReturn_adjacent_residue S B i) hlt⟩
    have hspan := allPositiveEdgeSpan c hL hlo hhi hstep
    have hlen := B.length_lower
    rw [ht] at hspan
    omega

private theorem t2_pair13_block_mixed (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 2)
    (hr : 10 ≤ pair12Count S.D) {K : ℕ}
    (hbudget1 : (pair12Count S.D - pair13Count S.D) + K ≤ 4)
    (hK : fullAxisExcess2 S + fullAxisExcess3 S +
      (pair12ExtraFinset S).card + (pair13ExtraFinset S).card ≤ K)
    (B : Pair13ExactBlock S) (hL : 2 ≤ B.length) :
    (∃ i : Fin (B.length - 1),
      pair13BlockReturn S B (edgeLeft i) < pair13BlockReturn S B (edgeRight i)) ∧
    (∃ i : Fin (B.length - 1),
      pair13BlockReturn S B (edgeRight i) < pair13BlockReturn S B (edgeLeft i)) := by
  let c := pair13BlockReturn S B
  have hlo : ∀ i, 1 ≤ c i := pair13BlockReturn_lower_t3 S hg hfull B
  have hhi : ∀ i, c i ≤ pair12Count S.D + fullAxisExcess2 S :=
    pair13BlockReturn_upper_t3 S B
  have hinj : Function.Injective c := pair13BlockReturn_injective_t3 S B
  have hK4 : K ≤ 4 := by omega
  have heK : (pair13ExtraFinset S).card + fullAxisExcess2 S ≤ K := by omega
  constructor
  · by_contra hn
    have hstep : ∀ i : Fin (B.length - 1),
        c (edgeRight i) < c (edgeLeft i) ∧
        pair12Count S.D ≤ c (edgeLeft i) - c (edgeRight i) := by
      intro i
      have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
        intro heq
        have hi := hinj heq
        have hv := congrArg Fin.val hi
        simp [edgeLeft, edgeRight] at hv
      have hlt : c (edgeRight i) < c (edgeLeft i) := by
        by_contra hnot
        have : c (edgeLeft i) < c (edgeRight i) := by omega
        exact hn ⟨i, this⟩
      exact ⟨hlt, pair13LocalReturn_step_down S (by omega)
        (pair13BlockReturn_adjacent_residue S B i) hlt⟩
    have hspan := allNegativeEdgeSpan c hL hlo hhi hstep
    have hlen : pair12Count S.D - 4 ≤ B.length := by
      have := B.length_lower
      omega
    have hmulle : pair12Count S.D * (pair12Count S.D - 5) ≤
        pair12Count S.D * (B.length - 1) := Nat.mul_le_mul_left _ (by omega)
    have hsub5 : pair12Count S.D - 5 + 5 = pair12Count S.D := by omega
    have hpoly : pair12Count S.D + 3 <
        pair12Count S.D * (pair12Count S.D - 5) := by nlinarith
    omega
  · by_contra hn
    have hstep : ∀ i : Fin (B.length - 1),
        c (edgeLeft i) < c (edgeRight i) ∧
        pair23Count S.D ≤ c (edgeRight i) - c (edgeLeft i) := by
      intro i
      have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
        intro heq
        have hi := hinj heq
        have hv := congrArg Fin.val hi
        simp [edgeLeft, edgeRight] at hv
      have hlt : c (edgeLeft i) < c (edgeRight i) := by
        by_contra hnot
        have : c (edgeRight i) < c (edgeLeft i) := by omega
        exact hn ⟨i, this⟩
      exact ⟨hlt, pair13LocalReturn_step_up S (by omega)
        (pair13BlockReturn_adjacent_residue S B i) hlt⟩
    have hspan := allPositiveEdgeSpan c hL hlo hhi hstep
    have hlen := B.length_lower
    rw [ht] at hspan
    omega

private theorem t2_thin_lowerBox_card (S : CyclicStaircase) {g : Point3}
    (hfull : FullSupport g) (ht : pair23Count S.D = 2)
    (hy : g.y = 1) (hz : g.z = 1) (hspos : 0 < pair13Count S.D)
    (hsx : pair13Count S.D ≤ g.x) :
    g.x - pair13Count S.D ≤ (lowerBoxFullOutsideCoreFinset S g).card := by
  classical
  let f : Fin (g.x - pair13Count S.D) →
      {p : Point3 // p ∈ lowerBoxFullOutsideCoreFinset S g} :=
    fun i => ⟨Point3.mk (pair13Count S.D + i.1) 1 1, by
      rw [mem_lowerBoxFullOutsideCoreFinset]
      refine ⟨⟨by simp; omega, by simpa [hy], by simpa [hz]⟩, ?_,
        ⟨by simp; omega, by norm_num, by norm_num⟩, ?_⟩
      · intro heq
        have hx := congrArg Point3.x heq
        simp at hx
        omega
      · intro hcore
        unfold FullCore at hcore
        simp only [Point3.x, Point3.y, Point3.z] at hcore
        omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hx := congrArg
      (fun p : {p : Point3 // p ∈ lowerBoxFullOutsideCoreFinset S g} => p.1.x) hij
    simpa [f] using hx
  have hc := Fintype.card_le_of_injective f hf
  simpa [f] using hc

private theorem pair12Extra_ge_count_of_pure1_cap (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hy : g.y = 1) (hz : g.z = 1) (hrpos : 0 < pair12Count S.D)
    (hrx : pair12Count S.D ≤ g.x)
    (hcap : pure1Intercept S ≤ g.x + 1) :
    pair12Count S.D ≤ (pair12ExtraFinset S).card := by
  classical
  let iLast : Fin (pair12Count S.D) := ⟨pair12Count S.D - 1, by omega⟩
  let b : Point3 := (orderedPair12Boundary S iLast).1
  have hbdata := (orderedPair12Boundary S iLast).2
  have hby : 2 ≤ b.y := by
    by_contra hnot
    have hby1 : b.y = 1 := by
      have := hbdata.2.2.1
      dsimp [b] at *
      omega
    have hpred := hbdata.1.pred2_mem hbdata.2.2.1
    have haxis : Point3.mk b.x 0 0 ∈ S.D := by
      have heq : Point3.mk b.x 0 0 =
          Point3.pred2 (orderedPair12Boundary S iLast).1 := by
        apply Point3.ext
        · simp [b, Point3.pred2]
        · simp [b, Point3.pred2, hby1]
        · simpa [b, Point3.pred2] using hbdata.2.2.2.symm
      rw [heq]
      exact hpred
    have hbxlt := (pure1_axis_mem_iff S b.x).mp haxis
    have hbx : b.x ≤ g.x := by omega
    have hpbox : Point3.mk g.x 1 0 ∈ lowerBoxFinset g := by
      rw [mem_lowerBoxFinset]
      refine ⟨⟨by rfl, by simpa [hy], by simp⟩, ?_⟩
      intro heq
      have he := congrArg Point3.z heq
      simp [hz] at he
    have hpD := lowerBoxFinset_subset_D hg hpbox
    have hbLe : b ≤ Point3.mk g.x 1 0 :=
      ⟨hbx, by simpa [hby1], by simpa [b] using hbdata.2.2.2⟩
    exact hbdata.1.not_mem (S.down_closed hbLe hpD)
  have hlast : 1 ≤ pair12Gamma S iLast := by
    dsimp [pair12Gamma, iLast, b] at *
    omega
  have hall : ∀ i : Fin (pair12Count S.D), 1 ≤ pair12Gamma S i := by
    intro i
    have hi : i ≤ iLast := by
      apply Fin.le_iff_val_le_val.mpr
      dsimp [iLast]
      omega
    exact le_trans hlast (pair12Gamma_noninc S hi)
  have hsum : pair12Count S.D ≤
      ∑ i : Fin (pair12Count S.D), pair12Gamma S i := by
    calc
      pair12Count S.D = ∑ _i : Fin (pair12Count S.D), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hall i
  have htotal := pair12Extra_card_ge_totalDefect S
  calc
    pair12Count S.D ≤ ∑ i : Fin (pair12Count S.D), pair12Gamma S i := hsum
    _ ≤ ∑ i : Fin (pair12Count S.D),
        (pair12Alpha S i + pair12Gamma S i) :=
      Finset.sum_le_sum fun _ _ => by omega
    _ ≤ (pair12ExtraFinset S).card := htotal

private theorem pair13Extra_ge_count_of_pure1_cap (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hy : g.y = 1) (hz : g.z = 1) (hspos : 0 < pair13Count S.D)
    (hsx : pair13Count S.D ≤ g.x)
    (hcap : pure1Intercept S ≤ g.x + 1) :
    pair13Count S.D ≤ (pair13ExtraFinset S).card := by
  classical
  let iLast : Fin (pair13Count S.D) := ⟨pair13Count S.D - 1, by omega⟩
  let b : Point3 := (orderedPair13Boundary S iLast).1
  have hbdata := (orderedPair13Boundary S iLast).2
  have hbz : 2 ≤ b.z := by
    by_contra hnot
    have hbz1 : b.z = 1 := by
      have := hbdata.2.2.2
      dsimp [b] at *
      omega
    have hpred := hbdata.1.pred3_mem hbdata.2.2.2
    have haxis : Point3.mk b.x 0 0 ∈ S.D := by
      have heq : Point3.mk b.x 0 0 =
          Point3.pred3 (orderedPair13Boundary S iLast).1 := by
        apply Point3.ext <;> simp [b, Point3.pred3, hbz1, hbdata.2.2.1]
      rw [heq]
      exact hpred
    have hbxlt := (pure1_axis_mem_iff S b.x).mp haxis
    have hbx : b.x ≤ g.x := by omega
    have hpbox : Point3.mk g.x 0 1 ∈ lowerBoxFinset g := by
      rw [mem_lowerBoxFinset]
      refine ⟨⟨by rfl, by simp, by simpa [hz]⟩, ?_⟩
      intro heq
      have he := congrArg Point3.y heq
      simp [hy] at he
    have hpD := lowerBoxFinset_subset_D hg hpbox
    have hbLe : b ≤ Point3.mk g.x 0 1 :=
      ⟨hbx, by simpa [b] using hbdata.2.2.1, by simpa [hbz1]⟩
    exact hbdata.1.not_mem (S.down_closed hbLe hpD)
  have hlast : 1 ≤ pair13Gamma S iLast := by
    dsimp [pair13Gamma, iLast, b] at *
    omega
  have hall : ∀ i : Fin (pair13Count S.D), 1 ≤ pair13Gamma S i := by
    intro i
    have hi : i ≤ iLast := by
      apply Fin.le_iff_val_le_val.mpr
      dsimp [iLast]
      omega
    exact le_trans hlast (pair13Gamma_noninc S hi)
  have hsum : pair13Count S.D ≤
      ∑ i : Fin (pair13Count S.D), pair13Gamma S i := by
    calc
      pair13Count S.D = ∑ _i : Fin (pair13Count S.D), 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hall i
  have htotal := pair13Extra_card_ge_totalDefect S
  calc
    pair13Count S.D ≤ ∑ i : Fin (pair13Count S.D), pair13Gamma S i := hsum
    _ ≤ ∑ i : Fin (pair13Count S.D),
        (pair13Alpha S i + pair13Gamma S i) :=
      Finset.sum_le_sum fun _ _ => by omega
    _ ≤ (pair13ExtraFinset S).card := htotal

private theorem t2_thin_relation12_impossible (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hy : g.y = 1) (hz : g.z = 1) (haxis : g.x + 1 < pure1Intercept S)
    {d : ℕ} (hd : 2 ≤ d)
    (hdbound : d - 1 ≤ pair12Count S.D + fullAxisExcess3 S)
    (hrel : S.p1 = S.p2 + (d : ZMod S.m) * S.p3) : False := by
  have hA : Point3.mk (g.x + 1) 0 0 ∈ S.D :=
    (pure1_axis_mem_iff S _).mpr haxis
  have hp3 := pair12_return_capacity_fullSupport S hg hfull
  have hdstd : d - 1 < pure3Intercept S := by
    unfold fullAxisExcess3 at hdbound
    omega
  have hB : Point3.mk 0 0 (d - 1) ∈ S.D :=
    (pure3_axis_mem_iff S _).mpr hdstd
  have hgres : (g.x : ZMod S.m) * S.p1 + S.p2 + S.p3 = 0 := by
    have hr := S.residue_rho g
    rw [fullSupport_return_eq_zero S hg hfull, S.residue_zero] at hr
    simpa [CyclicStaircase.residue, residueOf, hy, hz] using hr.symm
  have hres : S.residue (Point3.mk (g.x + 1) 0 0) =
      S.residue (Point3.mk 0 0 (d - 1)) := by
    unfold CyclicStaircase.residue residueOf
    simp only [Point3.x, Point3.y, Point3.z, Nat.cast_add, Nat.cast_one,
      Nat.cast_zero, zero_mul, add_zero]
    simp only [zero_add]
    change ((g.x : ZMod S.m) + 1) * S.p1 =
      ((d - 1 : ℕ) : ZMod S.m) * S.p3
    calc
      ((g.x : ZMod S.m) + 1) * S.p1 =
          (g.x : ZMod S.m) * S.p1 + S.p1 := by ring
      _ = (g.x : ZMod S.m) * S.p1 + S.p2 + (d : ZMod S.m) * S.p3 := by
        rw [hrel]
        ring
      _ = ((d - 1 : ℕ) : ZMod S.m) * S.p3 := by
        rw [Nat.cast_sub (by omega : 1 ≤ d)]
        push_cast
        linear_combination hgres <;> simp
  have heq := S.standard_eq_of_residue_eq hA hB hres
  have hx := congrArg Point3.x heq
  simp at hx

private theorem t2_thin_relation13_impossible (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hy : g.y = 1) (hz : g.z = 1) (haxis : g.x + 1 < pure1Intercept S)
    {d : ℕ} (hd : 2 ≤ d)
    (hdbound : d - 1 ≤ pair12Count S.D + fullAxisExcess2 S)
    (hrel : S.p1 = S.p3 + (d : ZMod S.m) * S.p2) : False := by
  have hA : Point3.mk (g.x + 1) 0 0 ∈ S.D :=
    (pure1_axis_mem_iff S _).mpr haxis
  have hp2 := pair12_intercept2_lower S
  have hdstd : d - 1 < pure2Intercept S := by
    unfold fullAxisExcess2 at hdbound
    omega
  have hB : Point3.mk 0 (d - 1) 0 ∈ S.D :=
    (pure2_axis_mem_iff S _).mpr hdstd
  have hgres : (g.x : ZMod S.m) * S.p1 + S.p2 + S.p3 = 0 := by
    have hr := S.residue_rho g
    rw [fullSupport_return_eq_zero S hg hfull, S.residue_zero] at hr
    simpa [CyclicStaircase.residue, residueOf, hy, hz] using hr.symm
  have hres : S.residue (Point3.mk (g.x + 1) 0 0) =
      S.residue (Point3.mk 0 (d - 1) 0) := by
    unfold CyclicStaircase.residue residueOf
    simp only [Point3.x, Point3.y, Point3.z, Nat.cast_add, Nat.cast_one,
      Nat.cast_zero, zero_mul, add_zero]
    simp only [zero_add]
    change ((g.x : ZMod S.m) + 1) * S.p1 =
      ((d - 1 : ℕ) : ZMod S.m) * S.p2
    calc
      ((g.x : ZMod S.m) + 1) * S.p1 =
          (g.x : ZMod S.m) * S.p1 + S.p1 := by ring
      _ = (g.x : ZMod S.m) * S.p1 + S.p3 + (d : ZMod S.m) * S.p2 := by
        rw [hrel]
        ring
      _ = ((d - 1 : ℕ) : ZMod S.m) * S.p2 := by
        rw [Nat.cast_sub (by omega : 1 ≤ d)]
        push_cast
        linear_combination hgres <;> simp
  have heq := S.standard_eq_of_residue_eq hA hB hres
  have hx := congrArg Point3.x heq
  simp at hx

private theorem t1_product_resource_lower (r x y z : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hcap : r + 2 ≤ x + y + z) (hyz : 2 ≤ y * z) :
    2 * r ≤ x * y * z + y * z := by
  have hyzsum : y + z ≤ y * z + 1 := by
    have hy' : (1 : ℤ) ≤ y := by exact_mod_cast hy
    have hz' : (1 : ℤ) ≤ z := by exact_mod_cast hz
    have hmul := mul_nonneg (show (0 : ℤ) ≤ y - 1 by omega)
      (show (0 : ℤ) ≤ z - 1 by omega)
    exact_mod_cast (show (y : ℤ) + z ≤ y * z + 1 by nlinarith)
  have hx' : (1 : ℤ) ≤ x := by exact_mod_cast hx
  have hyz' : (2 : ℤ) ≤ y * z := by exact_mod_cast hyz
  have hmul := mul_nonneg (show (0 : ℤ) ≤ x - 1 by omega)
    (show (0 : ℤ) ≤ y * z - 2 by omega)
  exact_mod_cast (show (2 : ℤ) * r ≤ x * y * z + y * z by nlinarith)

private theorem pair12_span_defect_lower {r s e A L : ℕ}
    (hs : 2 ≤ s) (he : e < r) (hL : 2 ≤ L)
    (hlen : r - e ≤ L) (hspan : s * (L - 1) ≤ r + A - 1) :
    r - 1 - ((r - 1) / s) ≤ e + A := by
  by_contra hnot
  have hdiv := Nat.lt_mul_div_succ (r - 1) (by omega : 0 < s)
  have hq : (r - 1) / s + A + 1 ≤ L - 1 := by omega
  have hmul := Nat.mul_le_mul_left s hq
  have hchain : s * ((r - 1) / s + A + 1) ≤ r + A - 1 :=
    le_trans hmul hspan
  have hexpand : s * ((r - 1) / s + A + 1) =
      s * ((r - 1) / s + 1) + s * A := by ring
  rw [hexpand] at hchain
  have hAle : A ≤ s * A := by nlinarith
  omega

private theorem pair13_span_defect_lower {r s e A L : ℕ}
    (hr : 2 ≤ r) (he : e < s) (hL : 2 ≤ L)
    (hlen : s - e ≤ L) (hspan : r * (L - 1) ≤ r + A - 1) :
    s - 1 ≤ e + A := by
  by_contra hnot
  have hq : A + 1 ≤ L - 1 := by omega
  have hmul := Nat.mul_le_mul_left r hq
  have hchain : r * (A + 1) ≤ r + A - 1 := le_trans hmul hspan
  have hexpand : r * (A + 1) = r + r * A := by ring
  rw [hexpand] at hchain
  have hAle : A ≤ r * A := by nlinarith
  omega

private theorem t2_thin_pair12_span (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 2)
    (hy : g.y = 1) (hz : g.z = 1)
    (haxis : g.x + 1 < pure1Intercept S)
    (he : (pair12ExtraFinset S).card < pair12Count S.D)
    (hL : 2 ≤ (pair12ExactBlock S he).length) :
    pair12Count S.D - 1 -
        ((pair12Count S.D - 1) / pair13Count S.D) ≤
      (pair12ExtraFinset S).card + fullAxisExcess3 S := by
  let B := pair12ExactBlock S he
  let c := pair12BlockReturn S B
  have hlo : ∀ i, 1 ≤ c i := pair12BlockReturn_lower_t3 S hg hfull B
  have hhi : ∀ i, c i ≤ pair12Count S.D + fullAxisExcess3 S :=
    pair12BlockReturn_upper_t3 S hg hfull B
  have hinj : Function.Injective c := pair12BlockReturn_injective_t3 S B
  have hstep : ∀ i : Fin (B.length - 1),
      c (edgeRight i) < c (edgeLeft i) ∧
      pair13Count S.D ≤ c (edgeLeft i) - c (edgeRight i) := by
    intro i
    have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
      intro heq
      have hi := hinj heq
      have hv := congrArg Fin.val hi
      simp [edgeLeft, edgeRight] at hv
    have hneg : ¬ c (edgeLeft i) < c (edgeRight i) := by
      intro hpos
      let d := c (edgeRight i) - c (edgeLeft i)
      have hd : 2 ≤ d := by
        have hd' := pair12LocalReturn_step_up S (by omega)
          (pair12BlockReturn_adjacent_residue S B i) hpos
        rw [ht] at hd'
        simpa [d, c] using hd'
      have hrel : S.p1 = S.p2 + (d : ZMod S.m) * S.p3 := by
        have hr := pair12BlockReturn_adjacent_residue S B i
        change (c (edgeRight i) : ZMod S.m) * S.p3 + S.p2 =
          (c (edgeLeft i) : ZMod S.m) * S.p3 + S.p1 at hr
        have hc : c (edgeLeft i) + d = c (edgeRight i) := by dsimp [d]; omega
        rw [← hc] at hr
        simp only [Nat.cast_add] at hr
        linear_combination -hr
      have hdbound : d - 1 ≤ pair12Count S.D + fullAxisExcess3 S := by
        dsimp [d, c]
        have hlo' := hlo (edgeLeft i)
        have hhi' := hhi (edgeRight i)
        dsimp [c] at hlo' hhi'
        omega
      exact t2_thin_relation12_impossible S hg hfull hy hz haxis hd hdbound hrel
    have hlt : c (edgeRight i) < c (edgeLeft i) := by omega
    exact ⟨hlt, pair12LocalReturn_step_down S (by omega)
      (pair12BlockReturn_adjacent_residue S B i) hlt⟩
  have hspan := allNegativeEdgeSpan c hL hlo hhi hstep
  exact pair12_span_defect_lower (by have := hord.1; omega) he hL B.length_lower hspan

private theorem t2_thin_pair13_span (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 2)
    (hy : g.y = 1) (hz : g.z = 1)
    (haxis : g.x + 1 < pure1Intercept S)
    (he : (pair13ExtraFinset S).card < pair13Count S.D)
    (hL : 2 ≤ (pair13ExactBlock S he).length) :
    pair13Count S.D - 1 ≤
      (pair13ExtraFinset S).card + fullAxisExcess2 S := by
  let B := pair13ExactBlock S he
  let c := pair13BlockReturn S B
  have hlo : ∀ i, 1 ≤ c i := pair13BlockReturn_lower_t3 S hg hfull B
  have hhi : ∀ i, c i ≤ pair12Count S.D + fullAxisExcess2 S :=
    pair13BlockReturn_upper_t3 S B
  have hinj : Function.Injective c := pair13BlockReturn_injective_t3 S B
  have hstep : ∀ i : Fin (B.length - 1),
      c (edgeRight i) < c (edgeLeft i) ∧
      pair12Count S.D ≤ c (edgeLeft i) - c (edgeRight i) := by
    intro i
    have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
      intro heq
      have hi := hinj heq
      have hv := congrArg Fin.val hi
      simp [edgeLeft, edgeRight] at hv
    have hneg : ¬ c (edgeLeft i) < c (edgeRight i) := by
      intro hpos
      let d := c (edgeRight i) - c (edgeLeft i)
      have hd : 2 ≤ d := by
        have hd' := pair13LocalReturn_step_up S (by have := hord.1; omega)
          (pair13BlockReturn_adjacent_residue S B i) hpos
        rw [ht] at hd'
        simpa [d, c] using hd'
      have hrel : S.p1 = S.p3 + (d : ZMod S.m) * S.p2 := by
        have hr := pair13BlockReturn_adjacent_residue S B i
        change (c (edgeRight i) : ZMod S.m) * S.p2 + S.p3 =
          (c (edgeLeft i) : ZMod S.m) * S.p2 + S.p1 at hr
        have hc : c (edgeLeft i) + d = c (edgeRight i) := by dsimp [d]; omega
        rw [← hc] at hr
        simp only [Nat.cast_add] at hr
        linear_combination -hr
      have hdbound : d - 1 ≤ pair12Count S.D + fullAxisExcess2 S := by
        dsimp [d, c]
        have hlo' := hlo (edgeLeft i)
        have hhi' := hhi (edgeRight i)
        dsimp [c] at hlo' hhi'
        omega
      exact t2_thin_relation13_impossible S hg hfull hy hz haxis hd hdbound hrel
    have hlt : c (edgeRight i) < c (edgeLeft i) := by omega
    exact ⟨hlt, pair13LocalReturn_step_down S (by omega)
      (pair13BlockReturn_adjacent_residue S B i) hlt⟩
  have hspan := allNegativeEdgeSpan c hL hlo hhi hstep
  exact pair13_span_defect_lower (by have := hord.2; have := hord.1; omega)
    he hL B.length_lower hspan

private theorem t2_mandatory_budget (r s E K : ℕ) (hs : 1 ≤ s) (hsr : s ≤ r)
    (hmand : r - 1 + K ≤ E)
    (hquad : 4 * E + (r - s + 1) ^ 2 ≤ 4 * s + 16) :
    (r - s) + K ≤ 4 ∧ (r - s) + 2 * K ≤ 8 := by
  let d := r - s
  have hrd : s + d = r := by dsimp [d]; omega
  have hq : 4 * K + (d + 3) ^ 2 ≤ 28 := by
    have hmandz : (r : ℤ) - 1 + K ≤ E := by
      have hz : (((r - 1 + K : ℕ) : ℤ)) ≤ (E : ℤ) := by exact_mod_cast hmand
      push_cast at hz
      rw [Nat.cast_sub (by omega : 1 ≤ r)] at hz
      exact hz
    have hquadz : (4 : ℤ) * E + ((r : ℤ) - s + 1) ^ 2 ≤ 4 * s + 16 := by
      exact_mod_cast hquad
    have hqz : (4 : ℤ) * K + ((r : ℤ) - s + 3) ^ 2 ≤ 28 := by
      nlinarith
    dsimp [d]
    have hdcast : (((r - s : ℕ) : ℤ)) = (r : ℤ) - s := by rw [Nat.cast_sub hsr]
    exact_mod_cast hqz
  have hd : d ≤ 2 := by nlinarith
  interval_cases d <;> norm_num at hq ⊢ <;> omega

set_option maxHeartbeats 800000 in
/-- Cofinal closure of the ordered full-support branch at `t = 1`. -/
theorem fullSupport_t1_cofinal_strict (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 1)
    (hr : 4 ≤ pair12Count S.D) : fullTarget S < S.m := by
  classical
  by_contra hnot
  have hmle : S.m ≤ fullTarget S := by omega
  have haccount := full_resource_accounting_lowerBox S hg hfull
  let E := fullResourceExcess S + (lowerBoxFullOutsideCoreFinset S g).card
  have hbase : fullM S + E ≤ fullTarget S := by
    calc
      fullM S + E ≤ fullM S + (puncturedFullCoreFinset S g).card +
          fullResourceExcess S + (lowerBoxFullOutsideCoreFinset S g).card := by
        dsimp [E]
        omega
      _ ≤ S.m := haccount
      _ ≤ fullTarget S := hmle
  have hbase' :
      3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
          Nat.choose (pair13Count S.D) 2 + Nat.choose 1 2 +
          E ≤
        quarterSquareCeil (pair12Count S.D + pair13Count S.D + 1 + 2) := by
    simpa [fullM, fullTarget, ht] using hbase
  have hE := t1_resource_budget (pair12Count S.D) (pair13Count S.D)
    E hord.2 hbase'
  have hsr : pair13Count S.D ≤ pair12Count S.D := hord.2
  have hcap := pair12_terminal_return_capacity_ordered S hg hfull hord
  by_cases hyz : 2 ≤ g.y * g.z
  · have hlower := t1_lowerBox_card S hfull ht
    have hplane := t1_pair23_rectangle_card S hg hfull ht
    have hres : (lowerBoxFullOutsideCoreFinset S g).card +
        (pair23ExtraFinset S).card ≤ E := by
      dsimp [E]
      unfold fullResourceExcess
      omega
    have hx := hfull.1
    have hy := hfull.2.1
    have hz := hfull.2.2
    have htwice := t1_product_resource_lower (pair12Count S.D)
      g.x g.y g.z hx hy hz hcap hyz
    have hbig : 2 * pair12Count S.D - 1 ≤
        g.x * g.y * g.z - 1 + g.y * g.z := by
      omega
    have hlowE : g.x * g.y * g.z - 1 + g.y * g.z ≤ E := by omega
    have : 2 * pair12Count S.D - 1 ≤ E := le_trans hbig hlowE
    omega
  · have hx := hfull.1
    have hy := hfull.2.1
    have hz := hfull.2.2
    have hyz1 : g.y = 1 ∧ g.z = 1 := by
      constructor <;> nlinarith
    rcases hyz1 with ⟨hy1, hz1⟩
    have hxr : pair12Count S.D ≤ g.x := by omega
    have hxs : pair13Count S.D ≤ g.x := le_trans hord.2 hxr
    have hlower := t1_lowerBox_card S hfull ht
    have hplane := t1_pair23_rectangle_card S hg hfull ht
    have hthin12 := pair12_thin_extra_card S hg hfull (by omega) hxr
    have hspos : 0 < pair13Count S.D := by
      have := hord.1
      omega
    have hthin13 := pair13_thin_extra_card S hg hfull hspos hxs
    have hresource :
        (lowerBoxFullOutsideCoreFinset S g).card +
            (pair23ExtraFinset S).card + (pair12ExtraFinset S).card +
              (pair13ExtraFinset S).card ≤ E := by
      dsimp [E]
      unfold fullResourceExcess
      omega
    have hresourceAxis :
        (lowerBoxFullOutsideCoreFinset S g).card +
            (pair23ExtraFinset S).card + (pair12ExtraFinset S).card +
              (pair13ExtraFinset S).card + fullAxisExcess1 S ≤ E := by
      dsimp [E]
      unfold fullResourceExcess
      omega
    have hlowerCard : g.x - 1 ≤ (lowerBoxFullOutsideCoreFinset S g).card := by
      simpa only [hy1, hz1, mul_one] using hlower
    have hplaneCard : 1 ≤ (pair23ExtraFinset S).card := by
      simpa only [hy1, hz1, one_mul] using hplane
    have hcap' : pair12Count S.D ≤ g.x := by
      rw [hy1, hz1] at hcap
      omega
    have hlowerTotal :
        (g.x - 1) + 1 + (g.x - pair12Count S.D + 1) +
            (g.x - pair13Count S.D + 1) ≤ E := by
      have hleft := Nat.add_le_add hlowerCard hplaneCard
      have hright := Nat.add_le_add hthin12 hthin13
      have hsum := Nat.add_le_add hleft hright
      exact le_trans (by simpa [Nat.add_assoc] using hsum) hresource
    have heqX : g.x = pair12Count S.D := by
      omega
    have heqS : pair13Count S.D = pair12Count S.D := by
      omega
    have hLBmin : pair12Count S.D - 1 ≤
        (lowerBoxFullOutsideCoreFinset S g).card := by
      simpa only [heqX] using hlowerCard
    have hPmin : 1 ≤ (pair23ExtraFinset S).card := hplaneCard
    have h12min : 1 ≤ (pair12ExtraFinset S).card := by
      simpa only [heqX, Nat.sub_self, zero_add] using hthin12
    have h13min : 1 ≤ (pair13ExtraFinset S).card := by
      simpa only [heqX, heqS, Nat.sub_self, zero_add] using hthin13
    have hEmax : E ≤ pair12Count S.D + 2 := by simpa only [heqS] using hE
    have haxis0 : fullAxisExcess1 S = 0 := by
      have hsumAxis : (pair12Count S.D - 1) + 1 + 1 + 1 +
          fullAxisExcess1 S ≤ E := by
        calc
          _ ≤ (lowerBoxFullOutsideCoreFinset S g).card +
              (pair23ExtraFinset S).card + (pair12ExtraFinset S).card +
                (pair13ExtraFinset S).card + fullAxisExcess1 S := by gcongr
          _ ≤ E := hresourceAxis
      omega
    have hextra12 : (pair12ExtraFinset S).card = 1 := by
      have hsum12 : (pair12Count S.D - 1) + 1 +
          (pair12ExtraFinset S).card + 1 ≤ E := by
        calc
          _ ≤ (lowerBoxFullOutsideCoreFinset S g).card +
              (pair23ExtraFinset S).card + (pair12ExtraFinset S).card +
                (pair13ExtraFinset S).card := by gcongr
          _ ≤ E := hresource
      omega
    have hintercept : pure1Intercept S = pair12Count S.D + 1 := by
      unfold fullAxisExcess1 at haxis0
      have hlow := pair12_intercept1_lower S
      omega
    have hpureCap : pure1Intercept S ≤ g.x + 1 := by
      rw [hintercept, heqX]
    have hextraBig := pair12Extra_ge_count_of_pure1_cap S hg hfull hy1 hz1
      (by omega) hxr hpureCap
    omega

set_option maxHeartbeats 800000 in
/-- Cofinal closure of the ordered full-support branch at `t = 2`. -/
theorem fullSupport_t2_cofinal_strict (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 2)
    (hr : 10 ≤ pair12Count S.D) : fullTarget S < S.m := by
  classical
  by_contra hnot
  have hmle : S.m ≤ fullTarget S := by omega
  have hs : 2 ≤ pair13Count S.D := by
    have := hord.1
    omega
  have hhole := coreHoleFinset_eq_empty_of_pair23_le_three S hg hfull hord (by omega)
  have hsimpP := simplexCard_le_punctured_add_hole S g hord
  rw [hhole] at hsimpP
  simp at hsimpP
  have hsimp2 : simplexCard (pair13Count S.D) 2 = pair13Count S.D - 1 := by
    simp [simplexCard]
  have horderedSub : orderedSimplexPunctured S g ⊆ puncturedFullCoreFinset S g := by
    intro p hp
    have hpf := Finset.mem_filter.mp hp
    rw [mem_puncturedFullCoreFinset]
    constructor
    · rcases Finset.mem_image.mp hpf.1 with ⟨i, _hi, rfl⟩
      exact orderedSimplex_fullCore S hord i
    · exact hpf.2
  have horderedCard : (orderedSimplexPunctured S g).card ≤
      (puncturedFullCoreFinset S g).card := Finset.card_le_card horderedSub
  have hcore : pair13Count S.D - 1 ≤
      (puncturedFullCoreFinset S g).card := by
    rw [← hsimp2]
    exact le_trans (by simpa [ht] using hsimpP) horderedCard
  let E := fullResourceExcess S + (lowerBoxFullOutsideCoreFinset S g).card
  have haccount := full_resource_accounting_lowerBox S hg hfull
  have hbudget :
      3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
          Nat.choose (pair13Count S.D) 2 + Nat.choose 2 2 +
          (pair13Count S.D - 1) + E ≤
        quarterSquareCeil (pair12Count S.D + pair13Count S.D + 2 + 2) := by
    have hbase : fullM S + (pair13Count S.D - 1) + E ≤ fullTarget S := by
      calc
        _ ≤ fullM S + (puncturedFullCoreFinset S g).card +
            fullResourceExcess S + (lowerBoxFullOutsideCoreFinset S g).card := by
          dsimp [E]
          omega
        _ ≤ S.m := haccount
        _ ≤ fullTarget S := hmle
    simpa [fullM, fullTarget, ht] using hbase
  have hbud := t2_resource_budget (pair12Count S.D) (pair13Count S.D) E
    hs hord.2 hbudget
  have hE : E ≤ pair13Count S.D + 3 := hbud.1
  have hquad := hbud.2
  have hcap := pair12_terminal_return_capacity_ordered S hg hfull hord
  by_cases hyz : 2 ≤ g.y * g.z
  · have hyzsum : 3 ≤ g.y + g.z := by
      have hy := hfull.2.1
      have hz := hfull.2.2
      nlinarith
    have hlower := lowerBox_x_arm_card S hg hfull ht hyzsum
    have hplane := pair23_lowerBox_arms_card S hg hfull ht
    let K := fullAxisExcess2 S + fullAxisExcess3 S +
      (pair12ExtraFinset S).card + (pair13ExtraFinset S).card
    have hKres : (lowerBoxFullOutsideCoreFinset S g).card +
        (pair23ExtraFinset S).card + K ≤ E := by
      dsimp [E, K]
      unfold fullResourceExcess
      omega
    have hmandatory : pair12Count S.D - 1 + K ≤ E := by
      have hxyz : pair12Count S.D - 1 ≤
          (g.x - 1) + ((g.y - 1) + (g.z - 1)) := by
        have hx := hfull.1
        have hy := hfull.2.1
        have hz := hfull.2.2
        omega
      omega
    have hKB := t2_mandatory_budget (pair12Count S.D) (pair13Count S.D)
      E K (by omega) hord.2 hmandatory hquad
    have hKdata : fullAxisExcess2 S + fullAxisExcess3 S +
        (pair12ExtraFinset S).card + (pair13ExtraFinset S).card ≤ K := by rfl
    have he12 : (pair12ExtraFinset S).card < pair12Count S.D := by
      dsimp [K] at hKB
      omega
    have he13 : (pair13ExtraFinset S).card < pair13Count S.D := by
      dsimp [K] at hKB
      omega
    let B12 := pair12ExactBlock S he12
    let B13 := pair13ExactBlock S he13
    have hL12 : 2 ≤ B12.length := by
      have := B12.length_lower
      dsimp [K] at hKB
      omega
    have hL13 : 2 ≤ B13.length := by
      have := B13.length_lower
      dsimp [K] at hKB
      omega
    have hm12 := t2_pair12_block_mixed S hg hfull hord ht hr hKB.1 hKdata B12 hL12
    have hm13 := t2_pair13_block_mixed S hg hfull hord ht hr hKB.1 hKdata B13 hL13
    exact fullSupport_mixedExactBlocks_impossible S hg hfull hord B12 B13 hL12 hL13
      (by omega) (by omega) hm12.1 hm12.2 hm13.1 hm13.2 hKdata (by omega)
  · have hx := hfull.1
    have hy := hfull.2.1
    have hz := hfull.2.2
    have hy1 : g.y = 1 := by nlinarith
    have hz1 : g.z = 1 := by nlinarith
    have hxr : pair12Count S.D ≤ g.x := by rw [hy1, hz1] at hcap; omega
    have hxs : pair13Count S.D ≤ g.x := le_trans hord.2 hxr
    have hlower := t2_thin_lowerBox_card S hfull ht hy1 hz1 (by omega) hxs
    have hthin12 := pair12_thin_extra_card S hg hfull (by omega) hxr
    have hthin13 := pair13_thin_extra_card S hg hfull (by omega) hxs
    have haxis : g.x + 1 < pure1Intercept S := by
      by_contra hn
      have hpure : pure1Intercept S ≤ g.x + 1 := Nat.le_of_not_gt hn
      have he12big := pair12Extra_ge_count_of_pure1_cap S hg hfull hy1 hz1
        (by omega) hxr hpure
      have he13big := pair13Extra_ge_count_of_pure1_cap S hg hfull hy1 hz1
        (by omega) hxs hpure
      have hres : (pair12ExtraFinset S).card +
          (pair13ExtraFinset S).card ≤ E := by
        dsimp [E]
        unfold fullResourceExcess
        omega
      omega
    have hA1 : g.x - pair12Count S.D + 1 ≤ fullAxisExcess1 S := by
      unfold fullAxisExcess1
      have hbase := pair12_intercept1_lower S
      omega
    have hspan12 : pair12Count S.D - 1 -
          ((pair12Count S.D - 1) / pair13Count S.D) ≤
        (pair12ExtraFinset S).card + fullAxisExcess3 S := by
      by_cases he : (pair12ExtraFinset S).card < pair12Count S.D
      · let B := pair12ExactBlock S he
        by_cases hL : 2 ≤ B.length
        · exact t2_thin_pair12_span S hg hfull hord ht hy1 hz1 haxis he hL
        · have hlen := B.length_lower
          have her : pair12Count S.D - 1 ≤ (pair12ExtraFinset S).card := by
            dsimp [B] at hlen hL
            omega
          calc
            _ ≤ pair12Count S.D - 1 := Nat.sub_le _ _
            _ ≤ (pair12ExtraFinset S).card := her
            _ ≤ (pair12ExtraFinset S).card + fullAxisExcess3 S := by omega
      · have her : pair12Count S.D - 1 ≤ (pair12ExtraFinset S).card := by omega
        calc
          _ ≤ pair12Count S.D - 1 := Nat.sub_le _ _
          _ ≤ (pair12ExtraFinset S).card := her
          _ ≤ (pair12ExtraFinset S).card + fullAxisExcess3 S := by omega
    have hspan13 : pair13Count S.D - 1 ≤
        (pair13ExtraFinset S).card + fullAxisExcess2 S := by
      by_cases he : (pair13ExtraFinset S).card < pair13Count S.D
      · let B := pair13ExactBlock S he
        by_cases hL : 2 ≤ B.length
        · exact t2_thin_pair13_span S hg hfull hord ht hy1 hz1 haxis he hL
        · have hlen := B.length_lower
          omega
      · omega
    have hresAll : fullAxisExcess1 S +
          (lowerBoxFullOutsideCoreFinset S g).card +
          ((pair12ExtraFinset S).card + fullAxisExcess3 S) +
          ((pair13ExtraFinset S).card + fullAxisExcess2 S) ≤ E := by
      dsimp [E]
      unfold fullResourceExcess
      omega
    let q := (pair12Count S.D - 1) / pair13Count S.D
    have hqmul : q * pair13Count S.D ≤ pair12Count S.D - 1 := by
      exact Nat.div_mul_le_self _ _
    have hq2 : 2 * q ≤ pair12Count S.D - 1 := by
      have := Nat.mul_le_mul_left q hs
      dsimp [q] at *
      nlinarith
    have hlarge : pair13Count S.D + 4 ≤
        2 * g.x - 1 - q := by
      dsimp [q]
      omega
    have hElower : pair13Count S.D + 4 ≤ E := by
      dsimp [q] at hlarge
      omega
    omega

end NSP3
