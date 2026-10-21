import NSP3.OrderedPairBoundaries

namespace NSP3

open scoped BigOperators

def PairDefectSource {q : ℕ} (α γ : Fin q → ℕ) :=
  Σ i : Fin q, Fin (α i) ⊕ Fin (γ i)

instance {q : ℕ} (α γ : Fin q → ℕ) : Fintype (PairDefectSource α γ) := by
  unfold PairDefectSource
  infer_instance

@[simp] theorem card_pairDefectSource {q : ℕ} (α γ : Fin q → ℕ) :
    Fintype.card (PairDefectSource α γ) = ∑ i, (α i + γ i) := by
  simp [PairDefectSource, Fintype.card_sigma]

private noncomputable def pair12DefectPoint (S : CyclicStaircase) :
    PairDefectSource (pair12Alpha S) (pair12Gamma S) → Point3
  | ⟨i, Sum.inl k⟩ =>
      Point3.mk (i.1 + 1 + k.1) (pair12Count S.D - i.1 + pair12Gamma S i) 0
  | ⟨i, Sum.inr k⟩ =>
      Point3.mk (i.1 + 1) (pair12Count S.D - i.1 + k.1) 0

private theorem pair12DefectPoint_injective (S : CyclicStaircase) :
    Function.Injective (pair12DefectPoint S) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  rcases a with k | k <;> rcases b with l | l
  · have hy := congrArg Point3.y h
    have hji : j ≤ i := by
      by_contra hn
      have hij : i < j := lt_of_not_ge hn
      have hg := pair12Gamma_noninc S (le_of_lt hij)
      dsimp [pair12DefectPoint] at hy
      omega
    have hij : i ≤ j := by
      by_contra hn
      have hji' : j < i := lt_of_not_ge hn
      have hg := pair12Gamma_noninc S (le_of_lt hji')
      dsimp [pair12DefectPoint] at hy
      omega
    have hijEq : i = j := le_antisymm hij hji
    subst j
    congr
    apply Fin.ext
    have hx := congrArg Point3.x h
    simpa [pair12DefectPoint] using hx
  · have hx := congrArg Point3.x h
    have hy := congrArg Point3.y h
    have hij : i ≤ j := by
      apply Fin.le_iff_val_le_val.mpr
      dsimp [pair12DefectPoint] at hx
      omega
    have hg := pair12Gamma_noninc S hij
    dsimp [pair12DefectPoint] at hx hy
    omega
  · have hx := congrArg Point3.x h
    have hy := congrArg Point3.y h
    have hji : j ≤ i := by
      apply Fin.le_iff_val_le_val.mpr
      dsimp [pair12DefectPoint] at hx
      omega
    have hg := pair12Gamma_noninc S hji
    dsimp [pair12DefectPoint] at hx hy
    omega
  · have hx := congrArg Point3.x h
    have hijEq : i = j := by
      apply Fin.ext
      dsimp [pair12DefectPoint] at hx
      omega
    subst j
    congr
    apply Fin.ext
    have hy := congrArg Point3.y h
    simpa [pair12DefectPoint] using hy

private theorem pair12DefectPoint_mem (S : CyclicStaircase)
    (u : PairDefectSource (pair12Alpha S) (pair12Gamma S)) :
    pair12DefectPoint S u ∈ pair12ExtraFinset S := by
  rcases u with ⟨i, k | k⟩
  · let b := (orderedPair12Boundary S i).1
    have hxbase := orderedPair12Boundary_x_baseline S i
    have hybase := orderedPair12Boundary_y_baseline S i
    have hxeq : b.x = i.1 + 1 + pair12Alpha S i := by
      dsimp [b, pair12Alpha]
      omega
    have hyeq : b.y = pair12Count S.D - i.1 + pair12Gamma S i := by
      dsimp [b, pair12Gamma]
      omega
    have hpred := (orderedPair12Boundary S i).2.1.pred1_mem
      (orderedPair12Boundary S i).2.2.1
    have hmem : pair12DefectPoint S ⟨i, Sum.inl k⟩ ∈ S.D := by
      apply S.down_closed (b := b.pred1) ?_ hpred
      constructor
      · simp [pair12DefectPoint, b, Point3.pred1, hxeq]
        omega
      · constructor
        · simp [pair12DefectPoint, b, Point3.pred1, hyeq]
        · simp [pair12DefectPoint, b, Point3.pred1]
    apply (mem_pair12ExtraFinset S _).mpr
    refine ⟨hmem, by simp [pair12DefectPoint], ?_, by simp [pair12DefectPoint], ?_⟩
    · have hypos := (orderedPair12Boundary S i).2.2.2.1
      simp [pair12DefectPoint]
    · simp [pair12DefectPoint]
      omega
  · let b := (orderedPair12Boundary S i).1
    have hxbase := orderedPair12Boundary_x_baseline S i
    have hybase := orderedPair12Boundary_y_baseline S i
    have hxeq : b.x = i.1 + 1 + pair12Alpha S i := by
      dsimp [b, pair12Alpha]
      omega
    have hyeq : b.y = pair12Count S.D - i.1 + pair12Gamma S i := by
      dsimp [b, pair12Gamma]
      omega
    have hpred := (orderedPair12Boundary S i).2.1.pred2_mem
      (orderedPair12Boundary S i).2.2.2.1
    have hmem : pair12DefectPoint S ⟨i, Sum.inr k⟩ ∈ S.D := by
      apply S.down_closed (b := b.pred2) ?_ hpred
      constructor
      · simp [pair12DefectPoint, b, Point3.pred2, hxeq]
      · constructor
        · simp [pair12DefectPoint, b, Point3.pred2, hyeq]
          omega
        · simp [pair12DefectPoint, b, Point3.pred2]
    apply (mem_pair12ExtraFinset S _).mpr
    refine ⟨hmem, by simp [pair12DefectPoint], ?_, by simp [pair12DefectPoint], ?_⟩
    · simp [pair12DefectPoint]
    · simp [pair12DefectPoint]
      omega

/-- F4.3 for plane 12: every alpha/gamma defect token injects into a
distinct positive cell beyond the canonical triangle. -/
theorem pair12Extra_card_ge_totalDefect (S : CyclicStaircase) :
    (∑ i : Fin (pair12Count S.D), (pair12Alpha S i + pair12Gamma S i)) ≤
      (pair12ExtraFinset S).card := by
  classical
  let f : PairDefectSource (pair12Alpha S) (pair12Gamma S) →
      {p : Point3 // p ∈ pair12ExtraFinset S} :=
    fun u => ⟨pair12DefectPoint S u, pair12DefectPoint_mem S u⟩
  have hf : Function.Injective f := by
    intro a b h
    apply pair12DefectPoint_injective S
    exact congrArg Subtype.val h
  have hc := Fintype.card_le_of_injective f hf
  simpa [f] using hc

private noncomputable def pair13DefectPoint (S : CyclicStaircase) :
    PairDefectSource (pair13Alpha S) (pair13Gamma S) → Point3
  | ⟨i, Sum.inl k⟩ =>
      Point3.mk (i.1 + 1 + k.1) 0 (pair13Count S.D - i.1 + pair13Gamma S i)
  | ⟨i, Sum.inr k⟩ =>
      Point3.mk (i.1 + 1) 0 (pair13Count S.D - i.1 + k.1)

private theorem pair13DefectPoint_injective (S : CyclicStaircase) :
    Function.Injective (pair13DefectPoint S) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  rcases a with k | k <;> rcases b with l | l
  · have hz := congrArg Point3.z h
    have hji : j ≤ i := by
      by_contra hn
      have hg := pair13Gamma_noninc S (le_of_lt (lt_of_not_ge hn))
      dsimp [pair13DefectPoint] at hz
      omega
    have hij : i ≤ j := by
      by_contra hn
      have hg := pair13Gamma_noninc S (le_of_lt (lt_of_not_ge hn))
      dsimp [pair13DefectPoint] at hz
      omega
    have hijEq : i = j := le_antisymm hij hji
    subst j
    congr
    apply Fin.ext
    have hx := congrArg Point3.x h
    simpa [pair13DefectPoint] using hx
  · have hx := congrArg Point3.x h
    have hz := congrArg Point3.z h
    have hij : i ≤ j := Fin.le_iff_val_le_val.mpr (by
      dsimp [pair13DefectPoint] at hx; omega)
    have hg := pair13Gamma_noninc S hij
    dsimp [pair13DefectPoint] at hx hz
    omega
  · have hx := congrArg Point3.x h
    have hz := congrArg Point3.z h
    have hji : j ≤ i := Fin.le_iff_val_le_val.mpr (by
      dsimp [pair13DefectPoint] at hx; omega)
    have hg := pair13Gamma_noninc S hji
    dsimp [pair13DefectPoint] at hx hz
    omega
  · have hx := congrArg Point3.x h
    have hijEq : i = j := by
      apply Fin.ext
      dsimp [pair13DefectPoint] at hx
      omega
    subst j
    congr
    apply Fin.ext
    have hz := congrArg Point3.z h
    simpa [pair13DefectPoint] using hz

private theorem pair13DefectPoint_mem (S : CyclicStaircase)
    (u : PairDefectSource (pair13Alpha S) (pair13Gamma S)) :
    pair13DefectPoint S u ∈ pair13ExtraFinset S := by
  rcases u with ⟨i, k | k⟩
  · let b := (orderedPair13Boundary S i).1
    have hxbase := orderedPair13Boundary_x_baseline S i
    have hzbase := orderedPair13Boundary_z_baseline S i
    have hxeq : b.x = i.1 + 1 + pair13Alpha S i := by
      dsimp [b, pair13Alpha]; omega
    have hzeq : b.z = pair13Count S.D - i.1 + pair13Gamma S i := by
      dsimp [b, pair13Gamma]; omega
    have hpred := (orderedPair13Boundary S i).2.1.pred1_mem
      (orderedPair13Boundary S i).2.2.1
    have hmem : pair13DefectPoint S ⟨i, Sum.inl k⟩ ∈ S.D := by
      apply S.down_closed (b := b.pred1) ?_ hpred
      refine ⟨?_, ?_, ?_⟩
      · simp [pair13DefectPoint, b, Point3.pred1, hxeq]; omega
      · simp [pair13DefectPoint, b, Point3.pred1]
      · simp [pair13DefectPoint, b, Point3.pred1, hzeq]
    apply (mem_pair13ExtraFinset S _).mpr
    refine ⟨hmem, by simp [pair13DefectPoint], by simp [pair13DefectPoint], ?_, ?_⟩
    · have hzpos := (orderedPair13Boundary S i).2.2.2.2
      simp [pair13DefectPoint]
    · simp [pair13DefectPoint]; omega
  · let b := (orderedPair13Boundary S i).1
    have hxbase := orderedPair13Boundary_x_baseline S i
    have hzbase := orderedPair13Boundary_z_baseline S i
    have hxeq : b.x = i.1 + 1 + pair13Alpha S i := by
      dsimp [b, pair13Alpha]; omega
    have hzeq : b.z = pair13Count S.D - i.1 + pair13Gamma S i := by
      dsimp [b, pair13Gamma]; omega
    have hpred := (orderedPair13Boundary S i).2.1.pred3_mem
      (orderedPair13Boundary S i).2.2.2.2
    have hmem : pair13DefectPoint S ⟨i, Sum.inr k⟩ ∈ S.D := by
      apply S.down_closed (b := b.pred3) ?_ hpred
      refine ⟨?_, ?_, ?_⟩
      · simp [pair13DefectPoint, b, Point3.pred3, hxeq]
      · simp [pair13DefectPoint, b, Point3.pred3]
      · simp [pair13DefectPoint, b, Point3.pred3, hzeq]; omega
    apply (mem_pair13ExtraFinset S _).mpr
    refine ⟨hmem, by simp [pair13DefectPoint], by simp [pair13DefectPoint], ?_, ?_⟩
    · simp [pair13DefectPoint]
    · simp [pair13DefectPoint]; omega

theorem pair13Extra_card_ge_totalDefect (S : CyclicStaircase) :
    (∑ i : Fin (pair13Count S.D), (pair13Alpha S i + pair13Gamma S i)) ≤
      (pair13ExtraFinset S).card := by
  classical
  let f : PairDefectSource (pair13Alpha S) (pair13Gamma S) →
      {p : Point3 // p ∈ pair13ExtraFinset S} :=
    fun u => ⟨pair13DefectPoint S u, pair13DefectPoint_mem S u⟩
  have hf : Function.Injective f := by
    intro a b h
    apply pair13DefectPoint_injective S
    exact congrArg Subtype.val h
  have hc := Fintype.card_le_of_injective f hf
  simpa [f] using hc

private noncomputable def pair23DefectPoint (S : CyclicStaircase) :
    PairDefectSource (pair23Alpha S) (pair23Gamma S) → Point3
  | ⟨i, Sum.inl k⟩ =>
      Point3.mk 0 (i.1 + 1 + k.1) (pair23Count S.D - i.1 + pair23Gamma S i)
  | ⟨i, Sum.inr k⟩ =>
      Point3.mk 0 (i.1 + 1) (pair23Count S.D - i.1 + k.1)

private theorem pair23DefectPoint_injective (S : CyclicStaircase) :
    Function.Injective (pair23DefectPoint S) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  rcases a with k | k <;> rcases b with l | l
  · have hz := congrArg Point3.z h
    have hji : j ≤ i := by
      by_contra hn
      have hg := pair23Gamma_noninc S (le_of_lt (lt_of_not_ge hn))
      dsimp [pair23DefectPoint] at hz
      omega
    have hij : i ≤ j := by
      by_contra hn
      have hg := pair23Gamma_noninc S (le_of_lt (lt_of_not_ge hn))
      dsimp [pair23DefectPoint] at hz
      omega
    have hijEq : i = j := le_antisymm hij hji
    subst j
    congr
    apply Fin.ext
    have hy := congrArg Point3.y h
    simpa [pair23DefectPoint] using hy
  · have hy := congrArg Point3.y h
    have hz := congrArg Point3.z h
    have hij : i ≤ j := Fin.le_iff_val_le_val.mpr (by
      dsimp [pair23DefectPoint] at hy; omega)
    have hg := pair23Gamma_noninc S hij
    dsimp [pair23DefectPoint] at hy hz
    omega
  · have hy := congrArg Point3.y h
    have hz := congrArg Point3.z h
    have hji : j ≤ i := Fin.le_iff_val_le_val.mpr (by
      dsimp [pair23DefectPoint] at hy; omega)
    have hg := pair23Gamma_noninc S hji
    dsimp [pair23DefectPoint] at hy hz
    omega
  · have hy := congrArg Point3.y h
    have hijEq : i = j := by
      apply Fin.ext
      dsimp [pair23DefectPoint] at hy
      omega
    subst j
    congr
    apply Fin.ext
    have hz := congrArg Point3.z h
    simpa [pair23DefectPoint] using hz

private theorem pair23DefectPoint_mem (S : CyclicStaircase)
    (u : PairDefectSource (pair23Alpha S) (pair23Gamma S)) :
    pair23DefectPoint S u ∈ pair23ExtraFinset S := by
  rcases u with ⟨i, k | k⟩
  · let b := (orderedPair23Boundary S i).1
    have hybase := orderedPair23Boundary_y_baseline S i
    have hzbase := orderedPair23Boundary_z_baseline S i
    have hyeq : b.y = i.1 + 1 + pair23Alpha S i := by
      dsimp [b, pair23Alpha]; omega
    have hzeq : b.z = pair23Count S.D - i.1 + pair23Gamma S i := by
      dsimp [b, pair23Gamma]; omega
    have hpred := (orderedPair23Boundary S i).2.1.pred2_mem
      (orderedPair23Boundary S i).2.2.2.1
    have hmem : pair23DefectPoint S ⟨i, Sum.inl k⟩ ∈ S.D := by
      apply S.down_closed (b := b.pred2) ?_ hpred
      refine ⟨?_, ?_, ?_⟩
      · simp [pair23DefectPoint, b, Point3.pred2]
      · simp [pair23DefectPoint, b, Point3.pred2, hyeq]; omega
      · simp [pair23DefectPoint, b, Point3.pred2, hzeq]
    apply (mem_pair23ExtraFinset S _).mpr
    refine ⟨hmem, by simp [pair23DefectPoint], by simp [pair23DefectPoint], ?_, ?_⟩
    · have hzpos := (orderedPair23Boundary S i).2.2.2.2
      simp [pair23DefectPoint]
    · simp [pair23DefectPoint]; omega
  · let b := (orderedPair23Boundary S i).1
    have hybase := orderedPair23Boundary_y_baseline S i
    have hzbase := orderedPair23Boundary_z_baseline S i
    have hyeq : b.y = i.1 + 1 + pair23Alpha S i := by
      dsimp [b, pair23Alpha]; omega
    have hzeq : b.z = pair23Count S.D - i.1 + pair23Gamma S i := by
      dsimp [b, pair23Gamma]; omega
    have hpred := (orderedPair23Boundary S i).2.1.pred3_mem
      (orderedPair23Boundary S i).2.2.2.2
    have hmem : pair23DefectPoint S ⟨i, Sum.inr k⟩ ∈ S.D := by
      apply S.down_closed (b := b.pred3) ?_ hpred
      refine ⟨?_, ?_, ?_⟩
      · simp [pair23DefectPoint, b, Point3.pred3]
      · simp [pair23DefectPoint, b, Point3.pred3, hyeq]
      · simp [pair23DefectPoint, b, Point3.pred3, hzeq]; omega
    apply (mem_pair23ExtraFinset S _).mpr
    refine ⟨hmem, by simp [pair23DefectPoint], by simp [pair23DefectPoint], ?_, ?_⟩
    · simp [pair23DefectPoint]
    · simp [pair23DefectPoint]; omega

theorem pair23Extra_card_ge_totalDefect (S : CyclicStaircase) :
    (∑ i : Fin (pair23Count S.D), (pair23Alpha S i + pair23Gamma S i)) ≤
      (pair23ExtraFinset S).card := by
  classical
  let f : PairDefectSource (pair23Alpha S) (pair23Gamma S) →
      {p : Point3 // p ∈ pair23ExtraFinset S} :=
    fun u => ⟨pair23DefectPoint S u, pair23DefectPoint_mem S u⟩
  have hf : Function.Injective f := by
    intro a b h
    apply pair23DefectPoint_injective S
    exact congrArg Subtype.val h
  have hc := Fintype.card_le_of_injective f hf
  simpa [f] using hc

/-- A concrete contiguous zero-defect block in a finite ordered profile. -/
structure ExactDefectBlock (q : ℕ) (α γ : Fin q → ℕ) (minLength : ℕ) where
  start : ℕ
  length : ℕ
  end_le : start + length ≤ q
  length_lower : minLength ≤ length
  alpha_zero : ∀ k (hk : k < length), α ⟨start + k, by omega⟩ = 0
  gamma_zero : ∀ k (hk : k < length), γ ⟨start + k, by omega⟩ = 0

/-- A positive value in a monotone profile forces at least that many positive
terms in its suffix. -/
theorem monotone_suffix_sum_lower {q : ℕ} {f : Fin q → ℕ}
    (hf : Monotone f) (i : Fin q) (hi : 0 < f i) :
    q - i.1 ≤ ∑ j, f j := by
  let s : Finset (Fin q) := Finset.Ici i
  have hlocal : ∑ j ∈ s, 1 ≤ ∑ j ∈ s, f j := by
    apply Finset.sum_le_sum
    intro j hj
    have hij : i ≤ j := Finset.mem_Ici.mp hj
    have := hf hij
    omega
  have hsub : ∑ j ∈ s, f j ≤ ∑ j : Fin q, f j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simp [s]
    · simp
  have hcard : ∑ _j ∈ s, 1 = q - i.1 := by
    simp [s]
  omega

/-- A positive value in an antitone profile forces a positive prefix. -/
theorem antitone_prefix_sum_lower {q : ℕ} {f : Fin q → ℕ}
    (hf : Antitone f) (i : Fin q) (hi : 0 < f i) :
    i.1 + 1 ≤ ∑ j, f j := by
  let s : Finset (Fin q) := Finset.Iic i
  have hlocal : ∑ j ∈ s, 1 ≤ ∑ j ∈ s, f j := by
    apply Finset.sum_le_sum
    intro j hj
    have hji : j ≤ i := Finset.mem_Iic.mp hj
    have := hf hji
    omega
  have hsub : ∑ j ∈ s, f j ≤ ∑ j : Fin q, f j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · simp [s]
    · simp
  have hcard : ∑ _j ∈ s, 1 = i.1 + 1 := by
    simp [s]
  omega

/-- Quantitative defect mass plus opposite monotonicities produces a contiguous
zero-defect block.  The chosen start is the total gamma mass, and the chosen
length is exactly `q-e`; this includes the edge case `q=1,e=0`. -/
noncomputable def exactBlock_of_defect_sum {q e : ℕ} {α γ : Fin q → ℕ}
    (hα : Monotone α) (hγ : Antitone γ)
    (hsum : (∑ i : Fin q, (α i + γ i)) ≤ e) (hqe : e < q) :
    ExactDefectBlock q α γ (q - e) := by
  let A := ∑ i, α i
  let G := ∑ i, γ i
  have hsplit : A + G = ∑ i : Fin q, (α i + γ i) := by
    simp only [A, G, Finset.sum_add_distrib]
  have hAG : A + G ≤ e := by omega
  have hend : G + (q - e) ≤ q := by omega
  refine
    { start := G
      length := q - e
      end_le := hend
      length_lower := by omega
      alpha_zero := ?_
      gamma_zero := ?_ }
  · intro k hk
    let i : Fin q := ⟨G + k, by omega⟩
    change α i = 0
    by_contra hn
    have hi : 0 < α i := Nat.pos_of_ne_zero hn
    have hsuf := monotone_suffix_sum_lower hα i hi
    have hAle : (∑ j, α j) ≤ A := by rfl
    dsimp [i] at hsuf
    omega
  · intro k hk
    let i : Fin q := ⟨G + k, by omega⟩
    change γ i = 0
    by_contra hn
    have hi : 0 < γ i := Nat.pos_of_ne_zero hn
    have hpre := antitone_prefix_sum_lower hγ i hi
    have hGeq : (∑ j, γ j) = G := by rfl
    dsimp [i] at hpre
    omega

abbrev Pair12ExactBlock (S : CyclicStaircase) :=
  ExactDefectBlock (pair12Count S.D) (pair12Alpha S) (pair12Gamma S)
    (pair12Count S.D - (pair12ExtraFinset S).card)

abbrev Pair13ExactBlock (S : CyclicStaircase) :=
  ExactDefectBlock (pair13Count S.D) (pair13Alpha S) (pair13Gamma S)
    (pair13Count S.D - (pair13ExtraFinset S).card)

abbrev Pair23ExactBlock (S : CyclicStaircase) :=
  ExactDefectBlock (pair23Count S.D) (pair23Alpha S) (pair23Gamma S)
    (pair23Count S.D - (pair23ExtraFinset S).card)

noncomputable def pair12ExactBlock_of_defect_bound (S : CyclicStaircase)
    (hdefect : (∑ i : Fin (pair12Count S.D), (pair12Alpha S i + pair12Gamma S i)) ≤
      (pair12ExtraFinset S).card)
    (hpos : (pair12ExtraFinset S).card < pair12Count S.D) :
    Pair12ExactBlock S :=
  exactBlock_of_defect_sum (pair12Alpha_nondec S) (pair12Gamma_noninc S)
    hdefect hpos

noncomputable def pair13ExactBlock_of_defect_bound (S : CyclicStaircase)
    (hdefect : (∑ i : Fin (pair13Count S.D), (pair13Alpha S i + pair13Gamma S i)) ≤
      (pair13ExtraFinset S).card)
    (hpos : (pair13ExtraFinset S).card < pair13Count S.D) :
    Pair13ExactBlock S :=
  exactBlock_of_defect_sum (pair13Alpha_nondec S) (pair13Gamma_noninc S)
    hdefect hpos

noncomputable def pair23ExactBlock_of_defect_bound (S : CyclicStaircase)
    (hdefect : (∑ i : Fin (pair23Count S.D), (pair23Alpha S i + pair23Gamma S i)) ≤
      (pair23ExtraFinset S).card)
    (hpos : (pair23ExtraFinset S).card < pair23Count S.D) :
    Pair23ExactBlock S :=
  exactBlock_of_defect_sum (pair23Alpha_nondec S) (pair23Gamma_noninc S)
    hdefect hpos

/-- Canonical plane-12 exact block obtained directly from the actual extra set. -/
noncomputable def pair12ExactBlock (S : CyclicStaircase)
    (hpos : (pair12ExtraFinset S).card < pair12Count S.D) : Pair12ExactBlock S :=
  pair12ExactBlock_of_defect_bound S (pair12Extra_card_ge_totalDefect S) hpos

/-- Canonical plane-13 exact block obtained directly from the actual extra set. -/
noncomputable def pair13ExactBlock (S : CyclicStaircase)
    (hpos : (pair13ExtraFinset S).card < pair13Count S.D) : Pair13ExactBlock S :=
  pair13ExactBlock_of_defect_bound S (pair13Extra_card_ge_totalDefect S) hpos

/-- Canonical plane-23 exact block obtained directly from the actual extra set. -/
noncomputable def pair23ExactBlock (S : CyclicStaircase)
    (hpos : (pair23ExtraFinset S).card < pair23Count S.D) : Pair23ExactBlock S :=
  pair23ExactBlock_of_defect_bound S (pair23Extra_card_ge_totalDefect S) hpos

theorem pair12Boundary_eq_diagonal_of_defects_zero (S : CyclicStaircase)
    (i : Fin (pair12Count S.D)) (ha : pair12Alpha S i = 0)
    (hg : pair12Gamma S i = 0) :
    (orderedPair12Boundary S i).1 =
      Point3.mk (i.1 + 1) (pair12Count S.D - i.1) 0 := by
  apply Point3.ext
  · have hb := orderedPair12Boundary_x_baseline S i
    dsimp [pair12Alpha] at ha
    change (orderedPair12Boundary S i).1.x = i.1 + 1
    omega
  · have hb := orderedPair12Boundary_y_baseline S i
    dsimp [pair12Gamma] at hg
    change (orderedPair12Boundary S i).1.y = pair12Count S.D - i.1
    omega
  · exact (orderedPair12Boundary S i).2.2.2.2

theorem pair13Boundary_eq_diagonal_of_defects_zero (S : CyclicStaircase)
    (i : Fin (pair13Count S.D)) (ha : pair13Alpha S i = 0)
    (hg : pair13Gamma S i = 0) :
    (orderedPair13Boundary S i).1 =
      Point3.mk (i.1 + 1) 0 (pair13Count S.D - i.1) := by
  apply Point3.ext
  · have hb := orderedPair13Boundary_x_baseline S i
    dsimp [pair13Alpha] at ha
    change (orderedPair13Boundary S i).1.x = i.1 + 1
    omega
  · exact (orderedPair13Boundary S i).2.2.2.1
  · have hb := orderedPair13Boundary_z_baseline S i
    dsimp [pair13Gamma] at hg
    change (orderedPair13Boundary S i).1.z = pair13Count S.D - i.1
    omega

theorem pair23Boundary_eq_diagonal_of_defects_zero (S : CyclicStaircase)
    (i : Fin (pair23Count S.D)) (ha : pair23Alpha S i = 0)
    (hg : pair23Gamma S i = 0) :
    (orderedPair23Boundary S i).1 =
      Point3.mk 0 (i.1 + 1) (pair23Count S.D - i.1) := by
  apply Point3.ext
  · exact (orderedPair23Boundary S i).2.2.1
  · have hb := orderedPair23Boundary_y_baseline S i
    dsimp [pair23Alpha] at ha
    change (orderedPair23Boundary S i).1.y = i.1 + 1
    omega
  · have hb := orderedPair23Boundary_z_baseline S i
    dsimp [pair23Gamma] at hg
    change (orderedPair23Boundary S i).1.z = pair23Count S.D - i.1
    omega

end NSP3
