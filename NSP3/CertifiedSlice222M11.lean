import NSP3.CertifiedSlice222M10
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
theorem slice222_m11_checked : sliceRowCheck ⟨2,2,2⟩ 11 = true := by decide
end NSP3
