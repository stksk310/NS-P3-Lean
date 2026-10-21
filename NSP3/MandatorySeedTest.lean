import NSP3.MandatorySeed

namespace NSP3

#check mandatorySeed
#check mem_mandatorySeed
#check mandatorySeed_isDownset
#check lowerBoxFinset_subset_mandatorySeed
#check mandatorySeed_subset_standardSet

example : Point3.mk 2 0 0 ∈
    mandatorySeed (FullResidualTuple.mk 2 0 0) (Point3.mk 0 0 0) := by
  set_option maxRecDepth 100000 in decide

example : Point3.mk 1 1 0 ∈
    mandatorySeed (FullResidualTuple.mk 2 0 0) (Point3.mk 0 0 0) := by
  set_option maxRecDepth 100000 in decide

example : Point3.mk 1 1 1 ∈
    mandatorySeed (FullResidualTuple.mk 2 2 2) (Point3.mk 2 0 0) := by
  set_option maxRecDepth 100000 in decide

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    mandatorySeed
      (FullResidualTuple.mk (pair12Count S.D) (pair13Count S.D)
        (pair23Count S.D)) g ⊆ S.D := by
  exact mandatorySeed_subset_standardSet S hg hfull

end NSP3
