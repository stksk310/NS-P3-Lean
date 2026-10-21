import NSP3.CertifiedEmpty311
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
theorem slice321_empty_checked : indexedSliceChecked [] ⟨3,2,1⟩ = true := by decide
end NSP3
