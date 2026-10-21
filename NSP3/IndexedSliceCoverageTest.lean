import NSP3.IndexedSliceCoverage
namespace NSP3
-- Exact equality pins the old domain, including all coefficient lifts.
example (q : FullResidualTuple) (m : ℕ) :
    indexedSliceRowCheck checkedCertificateRows q m = sliceRowCheck q m := rfl
example (q : FullResidualTuple) :
    indexedSliceChecked checkedCertificateRows q = sliceChecked q := rfl
-- Deleting every branch cannot cover this concrete surviving q322 state.
set_option maxRecDepth 1000000 in
example : indexedSliceRowCheck [] ⟨3,2,2⟩ 19 = false := by decide
end NSP3
