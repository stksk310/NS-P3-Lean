import NSP3.CertifiedCoverRows00

namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000

-- Candidate source data; a separate global coverage proof is required.
def certificateRows01 : List CertificateRow := [
  ⟨⟨2,2,2⟩,15,⟨1,2,1⟩,1,4,6⟩,
  ⟨⟨2,2,2⟩,15,⟨1,2,1⟩,1,9,11⟩,
  ⟨⟨2,2,2⟩,15,⟨1,2,1⟩,3,2,8⟩,
  ⟨⟨2,2,2⟩,15,⟨1,2,1⟩,3,7,13⟩,
  ⟨⟨2,2,2⟩,15,⟨2,1,1⟩,1,4,9⟩,
  ⟨⟨2,2,2⟩,15,⟨2,1,1⟩,1,9,4⟩,
  ⟨⟨2,2,2⟩,15,⟨2,1,1⟩,3,2,7⟩,
  ⟨⟨2,2,2⟩,15,⟨2,1,1⟩,3,7,2⟩,
  ⟨⟨3,2,2⟩,19,⟨1,2,1⟩,1,5,8⟩,
  ⟨⟨3,2,2⟩,19,⟨2,1,1⟩,1,4,13⟩
]

theorem certificateRows01_checked : certificateRows01.all certificateRowCheck = true := by
  decide

end NSP3
