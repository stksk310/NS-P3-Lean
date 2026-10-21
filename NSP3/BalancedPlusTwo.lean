import NSP3.BalancedResources
import NSP3.OrderedSimplex

namespace NSP3

private theorem balancedResourceExcess_two (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D)
    (ht : 2 ≤ pair23Count S.D) :
    2 ≤ balancedResourceExcess S := by
  rcases two_pairFamilies_originFree S hnf with h1213 | h1223 | h1323
  · have h12 := pair12_originFree_resource S hnf hord heq ht h1213.1
    have h13 := pair13_originFree_resource S hnf hord heq ht h1213.2
    unfold balancedResourceExcess
    omega
  · have h12 := pair12_originFree_resource S hnf hord heq ht h1223.1
    have h23 := pair23_originFree_resource S hnf hord heq ht h1223.2
    unfold balancedResourceExcess
    omega
  · have h13 := pair13_originFree_resource S hnf hord heq ht h1323.1
    have h23 := pair23_originFree_resource S hnf hord heq ht h1323.2
    unfold balancedResourceExcess
    omega

theorem noFull_balanced_plus_two_fullCore (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D)
    (ht : 2 ≤ pair23Count S.D) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + (fullCoreFinset S).card + 2 ≤ S.m := by
  have haccount := balanced_resource_accounting S hnf hord heq
  have hexcess := balancedResourceExcess_two S hnf hord heq ht
  omega

private theorem simplexCard_le_fullCore (S : CyclicStaircase)
    (hord : PairCountsOrdered S) :
    simplexCard (pair13Count S.D) (pair23Count S.D) ≤
      (fullCoreFinset S).card := by
  classical
  let target := {p : Point3 // p ∈ fullCoreFinset S}
  let f : OrderedSimplexSource (pair13Count S.D) (pair23Count S.D) → target :=
    fun i => ⟨orderedSimplexPoint (pair13Count S.D) (pair23Count S.D) i,
      (mem_fullCoreFinset S _).mpr (orderedSimplex_fullCore S hord i)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply orderedSimplexPoint_injective (pair13Count S.D) (pair23Count S.D)
    exact congrArg Subtype.val hij
  have hcard := Fintype.card_le_of_injective f hf
  have htarget : Fintype.card target = (fullCoreFinset S).card := by
    simp [target]
  rw [card_orderedSimplexSource, htarget] at hcard
  exact hcard

theorem noFull_balanced_plus_two (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D)
    (ht : 2 ≤ pair23Count S.D) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + simplexCard (pair13Count S.D) (pair23Count S.D) + 2 ≤ S.m := by
  have hfull := noFull_balanced_plus_two_fullCore S hnf hord heq ht
  have hsimp := simplexCard_le_fullCore S hord
  omega

end NSP3
