import NSP3.CompactCoverPoints

namespace NSP3

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

-- One admitted nontrivial row from the diagnostic, checked in the kernel.
example : verifyCoverReject (13 - (fastMandatorySeed ⟨2,2,2⟩ ⟨1,1,1⟩).card)
    ⟨2,2,2⟩ ⟨1,1,1⟩ (⟨1,3,9⟩ : ResidueWeights 13)
    (compactCoverPoints (⟨1,3,9⟩ : ResidueWeights 13)
      (fastMandatorySeed ⟨2,2,2⟩ ⟨1,1,1⟩) ⟨1,1,1⟩)
    (fastMandatorySeed ⟨2,2,2⟩ ⟨1,1,1⟩) = true := by decide

end NSP3
