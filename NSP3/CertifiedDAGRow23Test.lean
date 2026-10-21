import NSP3.CertifiedDAGRow23
import NSP3.CertifiedCandidateRows
namespace NSP3
#check certificateDAGRow23_checked
set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
example : certificateDAGRow23 ∈ certificateRows := by decide
example : certificateRowDAGCheck certificateDAGRow23 (certificateDAGNodes23.take 1) = false := by decide
example : certificateRowDAGCheck certificateDAGRow23 certificateDAGNodes23.tail = false := by decide
-- Test the completion contract generically: concrete canonical recursion type
-- elaboration would execute an unrelated expensive downset enumeration.
example (row : CertificateRow) [NeZero row.m] (nodes : List CoverDAGNode)
    (hv : certificateRowDAGCheck row nodes = true) (D : Finset Point3)
    (hD : D ∈ downsetCompletions
      (row.m - (mandatorySeed row.q row.g).card)
      row.m (certificateRowWeights row) (mandatorySeed row.q row.g)) :
    ¬ terminalMatches row.q row.m row.g D :=
  certificateRowDAGCheck_sound row nodes hv D hD
end NSP3
