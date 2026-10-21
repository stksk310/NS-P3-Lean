import NSP3.PuncturedCore
import NSP3.LowerBox
import NSP3.CoreHole

namespace NSP3

#check fullSupport_puncturedCore_mem
#check mem_lowerBoxFinset
#check lowerBoxFinset_subset_D
#check card_lowerBoxFinset

example : (lowerBoxFinset (Point3.mk 1 1 1)).card = 7 := by
  simpa using card_lowerBoxFinset (Point3.mk 1 1 1)
example : (lowerBoxFinset (Point3.mk 2 1 1)).card = 11 := by
  simpa using card_lowerBoxFinset (Point3.mk 2 1 1)
example : (lowerBoxFinset (Point3.mk 2 2 1)).card = 17 := by
  simpa using card_lowerBoxFinset (Point3.mk 2 2 1)

#check mem_puncturedFullCoreFinset
#check mem_coreHoleFinset
#check card_fullCore_partition
#check coreHoleFinset_eq_empty_of_pair23_le_three
#check coreHoleFinset_eq_empty_of_gap
#check deepestPuncture_pairCounts_eq_one
#check deepestPuncture_fullTarget_lt

end NSP3
