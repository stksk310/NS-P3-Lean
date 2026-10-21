import NSP3.FiniteUnitScaling

namespace NSP3

/-- Direct divisor-by-two-coordinates enumeration; never constructs m³ raw weights. -/
def divisorResidueWeights (m : ℕ) [NeZero m] : Finset (ResidueWeights m) :=
  ((Finset.range m).filter fun d => 0 < d ∧ d ∣ m).biUnion fun d =>
    ((Finset.univ : Finset (ZMod m)).product
      (Finset.univ : Finset (ZMod m))).image fun a =>
        (⟨(d : ZMod m),a.1,a.2⟩ : ResidueWeights m)

theorem mem_divisorResidueWeights {m : ℕ} [NeZero m] (w : ResidueWeights m) :
    w ∈ divisorResidueWeights m ↔
      ∃ d : ℕ, 0 < d ∧ d < m ∧ d ∣ m ∧ w.p1 = (d : ZMod m) := by
  simp only [divisorResidueWeights, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_range, Finset.mem_image, Finset.mem_product, Finset.mem_univ,
    true_and, and_true]
  constructor
  · rintro ⟨d, ⟨hdm, hdp, hd⟩, a, ha⟩
    exact ⟨d, hdp, hdm, hd, (congrArg ResidueWeights.p1 ha.2).symm⟩
  · rintro ⟨d, hdp, hdm, hd, heq⟩
    refine ⟨d, ⟨hdm, hdp, hd⟩, (w.p2,w.p3), ?_⟩
    cases w
    simp_all

theorem seed_injective_first_ne_zero {m : ℕ} (q : FullResidualTuple)
    (g : Point3) (hf : FullSupport g) (w : ResidueWeights m)
    (hi : residueInjectiveOn (mandatorySeed q g) w) : w.p1 ≠ 0 := by
  have hz : Point3.zero ∈ mandatorySeed q g := by
    apply lowerBoxFinset_subset_mandatorySeed q g
    rw [mem_lowerBoxFinset]
    refine ⟨?_, ?_⟩
    · exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
    · intro h
      have := congrArg Point3.x h
      simp only [Point3.zero_x] at this
      have := hf.1
      omega
  have he : Point3.e1 ∈ mandatorySeed q g := by
    apply lowerBoxFinset_subset_mandatorySeed q g
    rw [mem_lowerBoxFinset]
    refine ⟨?_, ?_⟩
    · change 1 ≤ g.x ∧ 0 ≤ g.y ∧ 0 ≤ g.z
      exact ⟨hf.1,Nat.zero_le _,Nat.zero_le _⟩
    · intro h
      have := congrArg Point3.y h
      simp only [Point3.e1_y] at this
      have := hf.2.1
      omega
  have hinj : Set.InjOn (residueWithWeights w)
      (mandatorySeed q g : Set Point3) := Finset.card_image_iff.mp hi
  intro h
  have heq : Point3.e1 = Point3.zero := hinj he hz (by
    simp [residueWithWeights,residueOf,Point3.e1,Point3.zero,h])
  have := congrArg Point3.x heq
  simp [Point3.e1,Point3.zero] at this

theorem enumeratedCheckerState_unit_scale_iff {m : ℕ} [NeZero m]
    (q : FullResidualTuple) (g : Point3) (u : (ZMod m)ˣ) (w : ResidueWeights m) :
    EnumeratedCheckerState q m g (scaleResidueWeights u w) ↔
      EnumeratedCheckerState q m g w := by
  simp only [EnumeratedCheckerState,mem_boundaryResidueWeights,
    residue_zero_unit_scale_iff,residueInjectiveOn_unit_scale_iff]

/-- Source-exact reduction by feasible seed filters and a complete unit action. -/
def ReducedCheckerState (q : FullResidualTuple) (m : ℕ) [NeZero m]
    (g : Point3) (w : ResidueWeights m) : Prop :=
  EnumeratedCheckerState q m g w ∧ SeedFeasible q m g ∧
    w ∈ divisorResidueWeights m

instance (q : FullResidualTuple) (m : ℕ) [NeZero m]
    (g : Point3) (w : ResidueWeights m) : Decidable (ReducedCheckerState q m g w) := by
  unfold ReducedCheckerState
  infer_instance

theorem actual_strictFailure_has_reducedCheckerState (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (hs : S.m < fullTarget S) :
    letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
    ∃ u : (ZMod S.m)ˣ, ReducedCheckerState
      ⟨pair12Count S.D,pair13Count S.D,pair23Count S.D⟩ S.m g
      (scaleResidueWeights u (actualResidueWeights S)) := by
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  let q : FullResidualTuple := ⟨pair12Count S.D,pair13Count S.D,pair23Count S.D⟩
  have hi := actualResidueWeights_injective_on_mandatorySeed S hg hf
  have hn := seed_injective_first_ne_zero q g hf (actualResidueWeights S) hi
  obtain ⟨u,d,hd,hpos,hlt,heq⟩ := exists_divisor_normalization (actualResidueWeights S) hn
  refine ⟨u, ?_, actual_seedFeasible S hg hf, ?_⟩
  · apply (enumeratedCheckerState_unit_scale_iff q g u (actualResidueWeights S)).mpr
    exact actual_strictFailure_has_enumeratedCheckerState S hg hf ho hs
  · exact (mem_divisorResidueWeights _).mpr ⟨d,hpos,hlt,hd,heq⟩

end NSP3
