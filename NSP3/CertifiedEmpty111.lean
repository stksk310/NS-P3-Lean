import NSP3.IndexedSliceCoverage
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
theorem slice111_empty_checked : indexedSliceChecked [] ⟨1,1,1⟩ = true := by decide
end NSP3
