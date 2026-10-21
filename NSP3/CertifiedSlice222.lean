import NSP3.CertifiedSlice222M15
namespace NSP3
set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000

private theorem slice222_small_checked :
    ∀ m ∈ Finset.range 10, sliceRowCheck ⟨2,2,2⟩ m = true := by decide

/-- All m in the exact q222 arithmetic interval, including empty weight slices.
This does not cover any other residual q. -/
theorem slice222_checked : sliceChecked ⟨2,2,2⟩ = true := by
  apply List.all_eq_true.mpr
  intro m hm
  have hu : m < 16 := by simpa [List.mem_range,quarterSquareCeil] using hm
  by_cases hl : m < 10
  · exact slice222_small_checked m (Finset.mem_range.mpr hl)
  · have hlo : 10 ≤ m := by omega
    interval_cases m
    · exact slice222_m10_checked
    · exact slice222_m11_checked
    · exact slice222_m12_checked
    · exact slice222_m13_checked
    · exact slice222_m14_checked
    · exact slice222_m15_checked

/-- Unconditional exhaustion of this one reduced q slice, not global L11. -/
theorem no_reduced_terminal_matches_q222 (m : ℕ) [NeZero m]
    (g : Point3) (w : ResidueWeights m) (hr : ReducedCheckerState ⟨2,2,2⟩ m g w)
    (D : Finset Point3)
    (hD : D ∈ downsetCompletions (m-(mandatorySeed ⟨2,2,2⟩ g).card) m w
      (mandatorySeed ⟨2,2,2⟩ g)) : ¬ terminalMatches ⟨2,2,2⟩ m g D :=
  no_terminal_of_sliceChecked _ slice222_checked m g w hr D hD

end NSP3
