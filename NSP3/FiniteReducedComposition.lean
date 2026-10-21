import NSP3.FiniteNormalizedState
import NSP3.FiniteBlockedFrontier
import NSP3.FiniteProductBoundaries

namespace NSP3

/-- The precise remaining global kernel obligation after source-exact unit reduction. -/
def ReducedNoTarget : Prop :=
  ∀ (q : FullResidualTuple) (m : ℕ) [NeZero m] (g : Point3) (w : ResidueWeights m),
    ReducedCheckerState q m g w →
    ∀ D ∈ downsetCompletions (m-(mandatorySeed q g).card) m w (mandatorySeed q g),
      ¬ terminalMatches q m g D

/-- Explicit final composition, conditional on the as-yet-unproved global
finite exhaustion. This theorem does not assert that ReducedNoTarget holds. -/
theorem fullSupport_ordered_sharp_of_reduced_exhaustion (hex : ReducedNoTarget)
    (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    fullTarget S ≤ S.m := by
  by_contra h
  have hs : S.m < fullTarget S := Nat.lt_of_not_ge h
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  obtain ⟨u,hu⟩ := actual_strictFailure_has_reducedCheckerState S hg hf ho hs
  let q : FullResidualTuple := ⟨pair12Count S.D,pair13Count S.D,pair23Count S.D⟩
  have hcov : S.D ∈ downsetCompletions (S.m-(mandatorySeed q g).card) S.m
      (scaleResidueWeights u (actualResidueWeights S)) (mandatorySeed q g) := by
    rw [downsetCompletions_unit_scale]
    exact actual_standardSet_mem_downsetCompletions S hg hf
  exact hex q S.m g (scaleResidueWeights u (actualResidueWeights S)) hu S.D hcov
    (actual_standardSet_terminalMatches S hg hf)

end NSP3
