import NSP3.CertifiedEmpty331
namespace NSP3
set_option maxRecDepth 1000000

theorem no_reduced_state_of_emptySliceChecked (q : FullResidualTuple)
    (hs : indexedSliceChecked [] q = true) (m : ℕ) [NeZero m]
    (g : Point3) (w : ResidueWeights m) : ¬ ReducedCheckerState q m g w := by
  intro hr
  obtain ⟨row,hrow,_⟩ := indexedSliceChecked_covers [] q hs m g w hr
  exact List.not_mem_nil hrow

theorem t1_empty_checked (q : FullResidualTuple) (ht : q.t = 1)
    (hq : q.IsResidual) : indexedSliceChecked [] q = true := by
  rcases q with ⟨r,s,t⟩
  change t = 1 at ht
  subst t
  have hsr : s ≤ r := hq.2.1
  have hts : 1 ≤ s := hq.1
  have hrl : r ≤ 3 := by
    rcases hq.2.2 with h | h | h | h | h | h <;> simp_all
  interval_cases r <;> interval_cases s
  · exact slice111_empty_checked
  · exact slice211_empty_checked
  · exact slice221_empty_checked
  · exact slice311_empty_checked
  · exact slice321_empty_checked
  · exact slice331_empty_checked

theorem no_reduced_terminal_matches_t1 (q : FullResidualTuple) (ht : q.t = 1)
    (m : ℕ) [NeZero m] (g : Point3) (w : ResidueWeights m)
    (hr : ReducedCheckerState q m g w) : False := by
  have hq := (mem_strictFailureArithmeticStateFinset _).mp hr.1.1 |>.1
  have hres := (mem_fullResidualTupleFinset q).mp
    ((mem_criticalResidualTupleFinset q).mp hq).1
  exact no_reduced_state_of_emptySliceChecked q (t1_empty_checked q ht hres) m g w hr
end NSP3
