import NSP3.FiniteCheckerAbstraction

namespace NSP3

theorem actual_mandatorySeed_card_le (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    (mandatorySeed ⟨pair12Count S.D, pair13Count S.D, pair23Count S.D⟩ g).card ≤ S.m := by
  rw [← S.card_D]
  exact Finset.card_le_card (mandatorySeed_subset_standardSet S hg hf)

theorem actual_boundary_not_mem_mandatorySeed (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    g ∉ mandatorySeed ⟨pair12Count S.D, pair13Count S.D, pair23Count S.D⟩ g := by
  exact fun h => hg.not_mem (mandatorySeed_subset_standardSet S hg hf h)

theorem actual_boundary_product_bound (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    (g.x+1)*(g.y+1)*(g.z+1)-1 ≤ S.m := by
  rw [← card_lowerBoxFinset]
  exact le_trans (Finset.card_le_card (lowerBoxFinset_subset_mandatorySeed
    ⟨pair12Count S.D, pair13Count S.D, pair23Count S.D⟩ g))
    (actual_mandatorySeed_card_le S hg hf)

/-- Parameter-only filters which preserve every actual full-support state. -/
def SeedFeasible (q : FullResidualTuple) (m : ℕ) (g : Point3) : Prop :=
  FullSupport g ∧ (mandatorySeed q g).card ≤ m ∧
    g ∉ mandatorySeed q g ∧ (g.x+1)*(g.y+1)*(g.z+1)-1 ≤ m

instance (q : FullResidualTuple) (m : ℕ) (g : Point3) :
    Decidable (SeedFeasible q m g) := by
  unfold SeedFeasible
  infer_instance

theorem actual_seedFeasible (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    SeedFeasible ⟨pair12Count S.D, pair13Count S.D, pair23Count S.D⟩ S.m g :=
  ⟨hf, actual_mandatorySeed_card_le S hg hf,
    actual_boundary_not_mem_mandatorySeed S hg hf, actual_boundary_product_bound S hg hf⟩

end NSP3
