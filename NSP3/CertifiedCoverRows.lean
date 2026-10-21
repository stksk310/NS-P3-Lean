import NSP3.CertifiedCoverRows01
import NSP3.CertifiedCandidateRows


namespace NSP3

-- Generated CANDIDATE data. Global reduced-state coverage is NOT established.
-- Every rejection below must be accepted by ordinary kernel reduction.
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000

def checkedCertificateRows : List CertificateRow :=
  certificateRows00 ++
  certificateRows01


theorem checked_certificateRows_checked : checkedCertificateRows.all certificateRowCheck = true := by
  simp only [checkedCertificateRows,List.all_append,
    certificateRows00_checked,
    certificateRows01_checked,
    Bool.and_self]

def CertifiedRowCoverage : Prop := RowCoverage certificateRows

theorem reducedNoTarget_of_certifiedRowCoverage
    (hchecks : ∀ row ∈ certificateRows, certificateRowCheck row = true)
    (h : CertifiedRowCoverage) :
    ReducedNoTarget := by
  exact reducedNoTarget_of_checkedRows certificateRows hchecks h

end NSP3
