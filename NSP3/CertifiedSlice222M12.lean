import NSP3.CertifiedSlice222M11
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
theorem slice222_m12_checked : sliceRowCheck ⟨2,2,2⟩ 12 = true := by decide
end NSP3
