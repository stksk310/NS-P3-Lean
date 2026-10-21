import NSP3.FiniteResidueWeights

namespace NSP3

#check ResidueWeights
#check allResidueWeights
#check boundaryResidueWeights
#check mem_boundaryResidueWeights
#check fullSupport_residue_eq_zero
#check actualResidueWeights_mem_boundary
#check residueInjectiveOn
#check actualResidueWeights_injective_on_standardSet
#check actualResidueWeights_injective_on_mandatorySeed

-- A nonunit coefficient is retained by the unquotiented enumeration.
example :
    ({ p1 := (2 : ZMod 6), p2 := 0, p3 := 0 } : ResidueWeights 6) ∈
      boundaryResidueWeights 6 (Point3.mk 3 0 0) := by decide

-- Distinct gcd lifts solving the same boundary equation are both retained.
example :
    ({ p1 := 0, p2 := 0, p3 := (0 : ZMod 6) } : ResidueWeights 6) ∈
      boundaryResidueWeights 6 (Point3.mk 0 0 2) ∧
    ({ p1 := 0, p2 := 0, p3 := (3 : ZMod 6) } : ResidueWeights 6) ∈
      boundaryResidueWeights 6 (Point3.mk 0 0 2) := by decide

end NSP3
