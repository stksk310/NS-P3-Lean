import NSP3.FiniteDownsetCompletion

namespace NSP3

/-- The load-bearing completion coverage bridge for an actual full boundary:
starting from the parameter-only mandatory seed, the exhaustive recursion
contains the complete standard set at the exact cardinality gap. -/
theorem actual_standardSet_mem_downsetCompletions
    (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    let q := FullResidualTuple.mk (pair12Count S.D) (pair13Count S.D)
      (pair23Count S.D)
    let seed := mandatorySeed q g
    S.D ∈ downsetCompletions (S.m - seed.card) S.m
      (actualResidueWeights S) seed := by
  let q := FullResidualTuple.mk (pair12Count S.D) (pair13Count S.D)
    (pair23Count S.D)
  let seed := mandatorySeed q g
  have hsub : seed ⊆ S.D := by
    simpa [seed, q] using mandatorySeed_subset_standardSet S hg hfull
  have hle : seed.card ≤ S.D.card := Finset.card_le_card hsub
  have hDm : S.D.card = S.m := S.card_D
  have hcard : seed.card + (S.m - seed.card) = S.D.card := by
    omega
  exact actual_mem_downsetCompletions (actualResidueWeights S)
    (S.m - seed.card) (mandatorySeed_isDownset q g) S.down_closed hsub
    (standardSet_subset_pointBox_m S)
    (actualResidueWeights_injective_on_standardSet S) hcard

end NSP3
