import NSP3.FullEdgeCollision
import NSP3.CoreHole

namespace NSP3

noncomputable def fullM (S : CyclicStaircase) : ℕ :=
  3 * pair12Count S.D + 1 + Nat.choose (pair12Count S.D) 2 +
    Nat.choose (pair13Count S.D) 2 + Nat.choose (pair23Count S.D) 2

noncomputable def fullResourceExcess (S : CyclicStaircase) : ℕ :=
  fullAxisExcess1 S + fullAxisExcess2 S + fullAxisExcess3 S +
    (pair12ExtraFinset S).card + (pair13ExtraFinset S).card +
    (pair23ExtraFinset S).card

noncomputable def lowerBoxFullOutsideCoreFinset (S : CyclicStaircase) (g : Point3) :
    Finset Point3 := by
  classical
  exact (lowerBoxFinset g).filter fun p => FullSupport p ∧ ¬ FullCore S p

@[simp] theorem mem_lowerBoxFullOutsideCoreFinset (S : CyclicStaircase) (g p : Point3) :
    p ∈ lowerBoxFullOutsideCoreFinset S g ↔
      p ≤ g ∧ p ≠ g ∧ FullSupport p ∧ ¬ FullCore S p := by
  classical
  simp [lowerBoxFullOutsideCoreFinset, and_assoc]

private noncomputable def threePlaneResourceFinset (S : CyclicStaircase) : Finset Point3 := by
  classical
  exact Finset.univ.image (threePlaneSourcePoint S)

private theorem mem_threePlaneResourceFinset (S : CyclicStaircase) (p : Point3) :
    p ∈ threePlaneResourceFinset S ↔ ∃ a, threePlaneSourcePoint S a = p := by
  classical
  simp [threePlaneResourceFinset]

private theorem card_threePlaneResourceFinset (S : CyclicStaircase) :
    (threePlaneResourceFinset S).card = Fintype.card (ThreePlaneSource S) := by
  classical
  rw [threePlaneResourceFinset, Finset.card_image_iff.mpr]
  · simp
  · exact fun _ _ _ _ h => threePlaneSourcePoint_injective S h

private theorem threePlaneResourceFinset_subset_D (S : CyclicStaircase) :
    threePlaneResourceFinset S ⊆ S.D := by
  intro p hp
  obtain ⟨a, rfl⟩ := (mem_threePlaneResourceFinset S p).mp hp
  exact threePlaneSourcePoint_mem S a

private theorem threePlaneResource_disjoint_punctured (S : CyclicStaircase) (g : Point3) :
    Disjoint (threePlaneResourceFinset S) (puncturedFullCoreFinset S g) := by
  rw [Finset.disjoint_left]
  intro p hp hpc
  obtain ⟨a, rfl⟩ := (mem_threePlaneResourceFinset S p).mp hp
  exact threePlaneSourcePoint_not_fullSupport S a
    (fullSupport_of_mem_puncturedFullCoreFinset hpc)

private theorem threePlaneResource_disjoint_lower (S : CyclicStaircase) (g : Point3) :
    Disjoint (threePlaneResourceFinset S) (lowerBoxFullOutsideCoreFinset S g) := by
  rw [Finset.disjoint_left]
  intro p hp hl
  obtain ⟨a, rfl⟩ := (mem_threePlaneResourceFinset S p).mp hp
  exact threePlaneSourcePoint_not_fullSupport S a
    ((mem_lowerBoxFullOutsideCoreFinset S g _).mp hl).2.2.1

private theorem punctured_disjoint_lower (S : CyclicStaircase) (g : Point3) :
    Disjoint (puncturedFullCoreFinset S g) (lowerBoxFullOutsideCoreFinset S g) := by
  rw [Finset.disjoint_left]
  intro p hp hl
  exact ((mem_lowerBoxFullOutsideCoreFinset S g p).mp hl).2.2.2
    ((mem_puncturedFullCoreFinset S g p).mp hp).1

private theorem threePlaneResource_disjoint_extra12 (S : CyclicStaircase) :
    Disjoint (threePlaneResourceFinset S) (pair12ExtraFinset S) := by
  rw [Finset.disjoint_left]
  intro p hp he
  obtain ⟨a, rfl⟩ := (mem_threePlaneResourceFinset S p).mp hp
  have he' := (mem_pair12ExtraFinset S _).mp he
  rcases a with u | i | j | k | q12 | q13 | q23 <;>
    simp [threePlaneSourcePoint] at he'
  have hq := Finset.mem_filter.mp q12.2
  have hr := Finset.mem_product.mp hq.1
  have hj := Finset.mem_range.mp hr.2
  omega

private theorem threePlaneResource_disjoint_extra13 (S : CyclicStaircase) :
    Disjoint (threePlaneResourceFinset S) (pair13ExtraFinset S) := by
  rw [Finset.disjoint_left]
  intro p hp he
  obtain ⟨a, rfl⟩ := (mem_threePlaneResourceFinset S p).mp hp
  have he' := (mem_pair13ExtraFinset S _).mp he
  rcases a with u | i | j | k | q12 | q13 | q23 <;>
    simp [threePlaneSourcePoint] at he'
  have hq := Finset.mem_filter.mp q13.2
  have hr := Finset.mem_product.mp hq.1
  have hj := Finset.mem_range.mp hr.2
  omega

private theorem threePlaneResource_disjoint_extra23 (S : CyclicStaircase) :
    Disjoint (threePlaneResourceFinset S) (pair23ExtraFinset S) := by
  rw [Finset.disjoint_left]
  intro p hp he
  obtain ⟨a, rfl⟩ := (mem_threePlaneResourceFinset S p).mp hp
  have he' := (mem_pair23ExtraFinset S _).mp he
  rcases a with u | i | j | k | q12 | q13 | q23 <;>
    simp [threePlaneSourcePoint] at he'
  have hq := Finset.mem_filter.mp q23.2
  have hr := Finset.mem_product.mp hq.1
  have hj := Finset.mem_range.mp hr.2
  omega

private theorem extras_pairwise_disjoint (S : CyclicStaircase) :
    Disjoint (pair12ExtraFinset S) (pair13ExtraFinset S) ∧
    Disjoint (pair12ExtraFinset S) (pair23ExtraFinset S) ∧
    Disjoint (pair13ExtraFinset S) (pair23ExtraFinset S) := by
  constructor
  · rw [Finset.disjoint_left]
    intro p h12 h13
    have a := (mem_pair12ExtraFinset S p).mp h12
    have b := (mem_pair13ExtraFinset S p).mp h13
    omega
  constructor
  · rw [Finset.disjoint_left]
    intro p h12 h23
    have a := (mem_pair12ExtraFinset S p).mp h12
    have b := (mem_pair23ExtraFinset S p).mp h23
    omega
  · rw [Finset.disjoint_left]
    intro p h13 h23
    have a := (mem_pair13ExtraFinset S p).mp h13
    have b := (mem_pair23ExtraFinset S p).mp h23
    omega

private noncomputable def planeResourceFinset (S : CyclicStaircase) : Finset Point3 :=
  threePlaneResourceFinset S ∪
    (pair12ExtraFinset S ∪ (pair13ExtraFinset S ∪ pair23ExtraFinset S))

private theorem planeResource_card (S : CyclicStaircase) :
    (planeResourceFinset S).card = Fintype.card (ThreePlaneSource S) +
      (pair12ExtraFinset S).card + (pair13ExtraFinset S).card +
      (pair23ExtraFinset S).card := by
  have he := extras_pairwise_disjoint S
  have hbase : Disjoint (threePlaneResourceFinset S)
      (pair12ExtraFinset S ∪ (pair13ExtraFinset S ∪ pair23ExtraFinset S)) :=
    Finset.disjoint_union_right.mpr ⟨threePlaneResource_disjoint_extra12 S,
      Finset.disjoint_union_right.mpr ⟨threePlaneResource_disjoint_extra13 S,
        threePlaneResource_disjoint_extra23 S⟩⟩
  unfold planeResourceFinset
  rw [Finset.card_union_of_disjoint hbase,
    Finset.card_union_of_disjoint
      (Finset.disjoint_union_right.mpr ⟨he.1, he.2.1⟩),
    Finset.card_union_of_disjoint he.2.2, card_threePlaneResourceFinset]
  omega

private theorem planeResource_subset_D (S : CyclicStaircase) :
    planeResourceFinset S ⊆ S.D := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact threePlaneResourceFinset_subset_D S hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact ((mem_pair12ExtraFinset S p).mp hp).1
  rcases Finset.mem_union.mp hp with hp | hp
  · exact ((mem_pair13ExtraFinset S p).mp hp).1
  · exact ((mem_pair23ExtraFinset S p).mp hp).1

private theorem planeResource_not_fullSupport (S : CyclicStaircase) {p : Point3}
    (hp : p ∈ planeResourceFinset S) : ¬ FullSupport p := by
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨a, rfl⟩ := (mem_threePlaneResourceFinset S p).mp hp
    exact threePlaneSourcePoint_not_fullSupport S a
  rcases Finset.mem_union.mp hp with hp | hp
  · intro h
    have he := (mem_pair12ExtraFinset S p).mp hp
    exact (Nat.ne_of_gt h.2.2) he.2.2.2.1
  rcases Finset.mem_union.mp hp with hp | hp
  · intro h
    have he := (mem_pair13ExtraFinset S p).mp hp
    exact (Nat.ne_of_gt h.2.1) he.2.2.1
  · intro h
    have he := (mem_pair23ExtraFinset S p).mp hp
    exact (Nat.ne_of_gt h.1) he.2.1

private theorem full_actualResource_card_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    pure1Intercept S + pure2Intercept S + pure3Intercept S - 2 +
      Nat.choose (pair12Count S.D) 2 + Nat.choose (pair13Count S.D) 2 +
      Nat.choose (pair23Count S.D) 2 + (pair12ExtraFinset S).card +
      (pair13ExtraFinset S).card + (pair23ExtraFinset S).card +
      (puncturedFullCoreFinset S g).card +
      (lowerBoxFullOutsideCoreFinset S g).card ≤ S.m := by
  classical
  let resources := planeResourceFinset S ∪
    (puncturedFullCoreFinset S g ∪ lowerBoxFullOutsideCoreFinset S g)
  have hdisj1 : Disjoint (planeResourceFinset S)
      (puncturedFullCoreFinset S g ∪ lowerBoxFullOutsideCoreFinset S g) :=
    Finset.disjoint_union_right.mpr ⟨by
      rw [Finset.disjoint_left]
      intro p hp hpc
      exact planeResource_not_fullSupport S hp
        (fullSupport_of_mem_puncturedFullCoreFinset hpc), by
      rw [Finset.disjoint_left]
      intro p hp hl
      exact planeResource_not_fullSupport S hp
        ((mem_lowerBoxFullOutsideCoreFinset S g p).mp hl).2.2.1⟩
  have hdisj2 := punctured_disjoint_lower S g
  have hsub : resources ⊆ S.D := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact planeResource_subset_D S hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact puncturedFullCoreFinset_subset_D S hg hfull hp
      · exact lowerBoxFinset_subset_D hg
          ((mem_lowerBoxFinset g p).mpr
            ⟨((mem_lowerBoxFullOutsideCoreFinset S g p).mp hp).1,
              ((mem_lowerBoxFullOutsideCoreFinset S g p).mp hp).2.1⟩)
  have hc := Finset.card_le_card hsub
  have hcard : resources.card = Fintype.card (ThreePlaneSource S) +
      (pair12ExtraFinset S).card + (pair13ExtraFinset S).card +
      (pair23ExtraFinset S).card + (puncturedFullCoreFinset S g).card +
      (lowerBoxFullOutsideCoreFinset S g).card := by
    dsimp [resources]
    rw [Finset.card_union_of_disjoint hdisj1, Finset.card_union_of_disjoint hdisj2,
      planeResource_card]
    omega
  rw [hcard, card_threePlaneSource] at hc
  rw [S.card_D] at hc
  have hp1 := (pure1Intercept_pure S).1
  have hp2 := (pure2Intercept_pure S).2.1
  have hp3 := (pure3Intercept_pure S).2.2
  omega

theorem full_resource_accounting_lowerBox (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    fullM S + (puncturedFullCoreFinset S g).card + fullResourceExcess S +
      (lowerBoxFullOutsideCoreFinset S g).card ≤ S.m := by
  have hc := full_actualResource_card_lower S hg hfull
  have h1 := pair12_intercept1_lower S
  have h2 := pair12_intercept2_lower S
  have h3 := pair12_return_capacity_fullSupport S hg hfull
  have hp1 := (pure1Intercept_pure S).1
  have hp2 := (pure2Intercept_pure S).2.1
  have hp3 := (pure3Intercept_pure S).2.2
  have he1 : pure1Intercept S = pair12Count S.D + 1 + fullAxisExcess1 S := by
    unfold fullAxisExcess1
    omega
  have he2 : pure2Intercept S = pair12Count S.D + 1 + fullAxisExcess2 S := by
    unfold fullAxisExcess2
    omega
  have he3 : pure3Intercept S = pair12Count S.D + 1 + fullAxisExcess3 S := by
    unfold fullAxisExcess3
    omega
  rw [he1, he2, he3] at hc
  unfold fullM fullResourceExcess fullAxisExcess1 fullAxisExcess2 fullAxisExcess3
  omega

theorem full_resource_accounting (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    fullM S + (puncturedFullCoreFinset S g).card + fullResourceExcess S ≤ S.m := by
  have h := full_resource_accounting_lowerBox S hg hfull
  omega

end NSP3
