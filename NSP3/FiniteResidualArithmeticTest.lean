import NSP3.FiniteResidualArithmetic

namespace NSP3

#check criticalResidualTupleFinset
#check mem_criticalResidualTupleFinset
#check criticalResidualTupleFinset_card
#check criticalResidualTuple_target_le
#check StrictFailureArithmeticState
#check strictFailureArithmeticStateFinset
#check mem_strictFailureArithmeticStateFinset
#check strictFailureArithmeticStateFinset_card

example : FullResidualTuple.mk 3 3 1 ∈ criticalResidualTupleFinset := by decide

example : FullResidualTuple.mk 7 2 2 ∉ criticalResidualTupleFinset := by decide
example : FullResidualTuple.mk 8 2 2 ∉ criticalResidualTupleFinset := by decide
example : FullResidualTuple.mk 9 2 2 ∉ criticalResidualTupleFinset := by decide
example : FullResidualTuple.mk 9 3 2 ∉ criticalResidualTupleFinset := by decide

example : FullResidualTuple.mk 7 2 2 ∈ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 8 2 2 ∈ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 9 2 2 ∈ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 9 3 2 ∈ fullResidualTupleFinset := by decide

example : criticalResidualTupleFinset.card = 203 :=
  criticalResidualTupleFinset_card

example : strictFailureArithmeticStateFinset.card = 4013 :=
  strictFailureArithmeticStateFinset_card

-- Arithmetic witness only; no staircase realizability is asserted.
example : (FullResidualTuple.mk 1 1 1, 4) ∈ strictFailureArithmeticStateFinset := by
  set_option maxRecDepth 100000 in
    decide

end NSP3
