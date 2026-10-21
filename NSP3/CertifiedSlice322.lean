import NSP3.CertifiedSlice322M20
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000
private theorem slice322_small_checked :
    ∀ m ∈ Finset.range 15, indexedSliceRowCheck checked322Rows ⟨3,2,2⟩ m = true := by decide

theorem slice322_checked : indexedSliceChecked checked322Rows ⟨3,2,2⟩ = true := by
  apply List.all_eq_true.mpr
  intro m hm
  have hu : m < 21 := by simpa [List.mem_range,quarterSquareCeil] using hm
  by_cases hl : m < 15
  · exact slice322_small_checked m (Finset.mem_range.mpr hl)
  · have hlo : 15 ≤ m := by omega
    interval_cases m
    · exact slice322_m15_checked
    · exact slice322_m16_checked
    · exact slice322_m17_checked
    · exact slice322_m18_checked
    · exact slice322_m19_checked
    · exact slice322_m20_checked

/-- Complete q322 reduced slice, not a global exhaustion theorem. -/
theorem no_reduced_terminal_matches_q322 (m : ℕ) [NeZero m]
    (g : Point3) (w : ResidueWeights m) (hr : ReducedCheckerState ⟨3,2,2⟩ m g w)
    (D : Finset Point3)
    (hD : D ∈ downsetCompletions (m-(mandatorySeed ⟨3,2,2⟩ g).card) m w
      (mandatorySeed ⟨3,2,2⟩ g)) : ¬ terminalMatches ⟨3,2,2⟩ m g D :=
  no_terminal_of_indexedSliceChecked checked322Rows checked322Rows_checked _
    slice322_checked m g w hr D hD
end NSP3
