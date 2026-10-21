import NSP3.FullResidualCompleteness

namespace NSP3

/-- The L11-only refinement of the frozen 207-set by the two arithmetic
conditions that every actual critical-envelope case satisfies. -/
def criticalResidualTupleFinset : Finset FullResidualTuple :=
  fullResidualTupleFinset.filter FullResidualTuple.largeStripArithmetic

@[simp] theorem mem_criticalResidualTupleFinset (q : FullResidualTuple) :
    q ∈ criticalResidualTupleFinset ↔
      q ∈ fullResidualTupleFinset ∧ q.largeStripArithmetic := by
  simp [criticalResidualTupleFinset]

/-- Kernel-reduced cardinality of the derived critical tuple set. -/
theorem criticalResidualTupleFinset_card :
    criticalResidualTupleFinset.card = 203 := by
  set_option maxRecDepth 100000 in
    decide

/-- The maximum target over the derived 203-tuple set. -/
def criticalResidualMaxTarget : ℕ :=
  criticalResidualTupleFinset.sup
    (fun q => quarterSquareCeil (q.r + q.s + q.t + 2))

theorem criticalResidualMaxTarget_eq : criticalResidualMaxTarget = 307 := by
  set_option maxRecDepth 100000 in
    decide

theorem criticalResidualTuple_target_le {q : FullResidualTuple}
    (hq : q ∈ criticalResidualTupleFinset) :
    quarterSquareCeil (q.r + q.s + q.t + 2) ≤ 307 := by
  set_option maxRecDepth 100000 in
    rw [← criticalResidualMaxTarget_eq]
    exact Finset.le_sup
      (s := criticalResidualTupleFinset)
      (f := fun q : FullResidualTuple =>
        quarterSquareCeil (q.r + q.s + q.t + 2)) hq

/-- A purely arithmetic strict-failure state.  This does not assert
realizability by a cyclic staircase. -/
abbrev StrictFailureArithmeticState := FullResidualTuple × ℕ

/-- The complete arithmetic envelope satisfying baseline <= m < target. -/
def strictFailureArithmeticStateFinset : Finset StrictFailureArithmeticState :=
  (criticalResidualTupleFinset.product (Finset.range 307)).filter fun a =>
    fullResidualM a.1.r a.1.s a.1.t ≤ a.2 ∧
      a.2 < quarterSquareCeil (a.1.r + a.1.s + a.1.t + 2)

set_option maxRecDepth 100000 in
@[simp] theorem mem_strictFailureArithmeticStateFinset
    (a : StrictFailureArithmeticState) :
    a ∈ strictFailureArithmeticStateFinset ↔
      a.1 ∈ criticalResidualTupleFinset ∧
      fullResidualM a.1.r a.1.s a.1.t ≤ a.2 ∧
      a.2 < quarterSquareCeil (a.1.r + a.1.s + a.1.t + 2) := by
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨hbox, hbounds⟩
    exact ⟨(Finset.mem_product.mp hbox).1, hbounds⟩
  · rintro ⟨hq, hlower, hupper⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, hlower, hupper⟩
    exact Finset.mem_product.mpr
      ⟨hq, Finset.mem_range.mpr (lt_of_lt_of_le hupper
        (criticalResidualTuple_target_le hq))⟩

set_option maxHeartbeats 10000000 in
/-- Diagnostic size of the complete arithmetic envelope, checked by ordinary kernel reduction. -/
theorem strictFailureArithmeticStateFinset_card :
    strictFailureArithmeticStateFinset.card = 4013 := by
  set_option maxRecDepth 100000 in
    decide

end NSP3
