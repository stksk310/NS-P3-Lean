import NSP3.Certified322Rows
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
theorem slice322_m15_checked : indexedSliceRowCheck checked322Rows ⟨3,2,2⟩ 15 = true := by
  decide
end NSP3
