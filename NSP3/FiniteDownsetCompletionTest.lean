import NSP3.FiniteDownsetCompletion

namespace NSP3

#check extensionCandidates
#check mem_extensionCandidates
#check insert_isDownset_of_mem_extensionCandidates
#check exists_actual_extensionCandidate
#check downsetCompletions
#check actual_mem_downsetCompletions

private def binaryWeights : ResidueWeights 2 :=
  { p1 := 1, p2 := 1, p3 := 1 }

-- The root can genuinely branch in more than one direction.
example : Point3.e1 ∈ extensionCandidates 2 binaryWeights {Point3.zero} ∧
    Point3.e2 ∈ extensionCandidates 2 binaryWeights {Point3.zero} := by
  decide

example : insert Point3.e1 {Point3.zero} ∈
    downsetCompletions 1 2 binaryWeights {Point3.zero} ∧
    insert Point3.e2 {Point3.zero} ∈
      downsetCompletions 1 2 binaryWeights {Point3.zero} := by
  decide

end NSP3
