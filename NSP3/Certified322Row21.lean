import NSP3.Certified322Row20
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
def certificate322Row21 : CertificateRow := ⟨⟨3,2,2⟩,20,⟨1,1,1⟩,4,1,15⟩
theorem certificate322Row21_checked : certificateRowCheck certificate322Row21 = true := by
  decide
end NSP3
