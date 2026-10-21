import NSP3.CertifiedRowVerifier

namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000

-- Candidate source data; a separate global coverage proof is required.
def certificateRows00 : List CertificateRow := [
  ⟨⟨2,2,2⟩,13,⟨1,1,1⟩,1,3,9⟩,
  ⟨⟨2,2,2⟩,13,⟨1,1,1⟩,1,9,3⟩,
  ⟨⟨2,2,2⟩,15,⟨1,1,1⟩,1,3,11⟩,
  ⟨⟨2,2,2⟩,15,⟨1,1,1⟩,1,11,3⟩,
  ⟨⟨2,2,2⟩,15,⟨1,1,1⟩,3,1,11⟩,
  ⟨⟨2,2,2⟩,15,⟨1,1,1⟩,3,11,1⟩,
  ⟨⟨2,2,2⟩,15,⟨1,1,2⟩,1,6,4⟩,
  ⟨⟨2,2,2⟩,15,⟨1,1,2⟩,1,11,9⟩,
  ⟨⟨2,2,2⟩,15,⟨1,1,2⟩,3,8,2⟩,
  ⟨⟨2,2,2⟩,15,⟨1,1,2⟩,3,13,7⟩
]

theorem certificateRows00_checked : certificateRows00.all certificateRowCheck = true := by
  decide

end NSP3
