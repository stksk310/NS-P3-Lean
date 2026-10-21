import NSP3.CertifiedRowVerifier
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
def certificate322Row20 : CertificateRow := ⟨⟨3,2,2⟩,20,⟨1,1,1⟩,1,4,15⟩
theorem certificate322Row20_checked : certificateRowCheck certificate322Row20 = true := by
  decide
end NSP3
