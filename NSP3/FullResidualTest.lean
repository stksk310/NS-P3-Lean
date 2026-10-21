import NSP3.FullResidual

namespace NSP3

#check FullResidualTuple
#check fullResidualTupleFinset
#check fullResidualTupleFinset_card

example : FullResidualTuple.mk 3 3 1 ∈ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 9 9 2 ∈ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 15 15 3 ∈ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 16 15 3 ∉ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 8 8 4 ∈ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 9 9 4 ∉ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 6 6 5 ∈ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 7 7 5 ∉ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 6 6 6 ∈ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 7 7 6 ∉ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 10 2 2 ∉ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 4 1 1 ∉ fullResidualTupleFinset := by decide
example : FullResidualTuple.mk 0 0 0 ∉ fullResidualTupleFinset := by decide

example : fullResidualTupleFinset.card = 207 := fullResidualTupleFinset_card

end NSP3
