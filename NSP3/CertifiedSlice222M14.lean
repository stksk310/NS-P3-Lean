import NSP3.CertifiedSlice222M13
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
theorem slice222_m14_checked : sliceRowCheck ⟨2,2,2⟩ 14 = true := by decide
end NSP3
