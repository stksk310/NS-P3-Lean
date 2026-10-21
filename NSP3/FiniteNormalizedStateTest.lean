import NSP3.FiniteNormalizedState

namespace NSP3

-- A normalized enumerator must retain nonunit first coefficients and all lifts.
example : (⟨2,3,5⟩ : ResidueWeights 30) ∈ divisorResidueWeights 30 := by
  exact (mem_divisorResidueWeights _).mpr ⟨2,by decide,by decide,by decide,rfl⟩
example : (⟨2,1,0⟩ : ResidueWeights 6) ∈ divisorResidueWeights 6 := by
  exact (mem_divisorResidueWeights _).mpr ⟨2,by decide,by decide,by decide,rfl⟩
example : (⟨2,1,3⟩ : ResidueWeights 6) ∈ divisorResidueWeights 6 := by
  exact (mem_divisorResidueWeights _).mpr ⟨2,by decide,by decide,by decide,rfl⟩

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (hs : S.m < fullTarget S) :
    letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
    ∃ u : (ZMod S.m)ˣ, ReducedCheckerState
      ⟨pair12Count S.D,pair13Count S.D,pair23Count S.D⟩ S.m g
      (scaleResidueWeights u (actualResidueWeights S)) :=
  actual_strictFailure_has_reducedCheckerState S hg hf ho hs

end NSP3
