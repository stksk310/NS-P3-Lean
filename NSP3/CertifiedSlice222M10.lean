import NSP3.CertifiedSliceCoverage
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
theorem slice222_m10_checked : sliceRowCheck ⟨2,2,2⟩ 10 = true := by decide
end NSP3
