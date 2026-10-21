import NSP3.FiniteCheckerState

namespace NSP3

#check pointBox
#check mem_pointBox
#check boundedMinimalComplements
#check mem_boundedMinimalComplements
#check strictFailure_D_subset_pointBox307
#check strictFailure_fullBoundary_mem_pointBox307
#check strictFailure_fullBoundary_mem_boundedMinimalComplements307
#check standardSet_subset_pointBox_m
#check fullSupport_minimalComplement_mem_pointBox_succ_m

example : Point3.mk 2 3 4 ∈ pointBox 5 := by decide
example : Point3.mk 5 0 0 ∉ pointBox 5 := by decide

example (S : CyclicStaircase) : S.D ⊆ pointBox S.m := by
  exact standardSet_subset_pointBox_m S

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    g ∈ pointBox (S.m + 1) := by
  exact fullSupport_minimalComplement_mem_pointBox_succ_m S hg hfull

end NSP3
