import NSP3.CertifiedEmpty321
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
theorem slice331_empty_checked : indexedSliceChecked [] ⟨3,3,1⟩ = true := by decide
end NSP3
