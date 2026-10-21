import NSP3.CertifiedSlice322

namespace NSP3
-- Catches a missing end-to-end non-q222 slice certificate, not a diagnostic count.
#check no_reduced_terminal_matches_q322
set_option maxRecDepth 1000000
example : certificate322Row20 ∈ certificateRows := by decide
example : certificate322Row21 ∈ certificateRows := by decide
example : certificate322Row22 ∈ certificateRows := by decide
example : indexedSliceChecked checked322Rows ⟨3,2,2⟩ = true := slice322_checked
end NSP3
