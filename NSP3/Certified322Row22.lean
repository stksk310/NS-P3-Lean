import NSP3.Certified322Row21
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
def certificate322Row22 : CertificateRow := ⟨⟨3,2,2⟩,20,⟨1,1,1⟩,4,11,5⟩
theorem certificate322Row22_checked : certificateRowCheck certificate322Row22 = true := by
  decide
end NSP3
