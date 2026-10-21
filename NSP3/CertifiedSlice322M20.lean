import NSP3.CertifiedSlice322M19
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
theorem slice322_m20_checked : indexedSliceRowCheck checked322Rows ⟨3,2,2⟩ 20 = true := by
  decide
end NSP3
