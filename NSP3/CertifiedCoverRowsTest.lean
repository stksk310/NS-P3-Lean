import NSP3.CertifiedCoverRows

namespace NSP3

set_option maxRecDepth 100000

example : certificateRowCheck ⟨⟨0,0,0⟩,0,⟨1,1,1⟩,0,0,0⟩ = false := by decide
example : certificateRowCheck ⟨⟨0,0,0⟩,7,⟨1,1,1⟩,1,2,4⟩ = false := by decide
example : certificateRowCheck ⟨⟨2,2,2⟩,13,⟨1,1,1⟩,0,0,0⟩ = false := by decide

example : checkedCertificateRows.all certificateRowCheck = true := checked_certificateRows_checked
example : checkedCertificateRows.length = 20 := by decide
-- Length is a checked data property, never a substitute for RowCoverage.
example : certificateRows.length = 160 := by decide
example (hc : ∀ row ∈ certificateRows, certificateRowCheck row = true)
    (h : CertifiedRowCoverage) : ReducedNoTarget :=
  reducedNoTarget_of_certifiedRowCoverage hc h

end NSP3
