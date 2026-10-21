import NSP3.FiniteResidualArithmetic

namespace NSP3

private noncomputable def xAxisBelow (q : Point3) : Finset Point3 :=
  (Finset.range (q.x + 1)).image fun i => Point3.mk i 0 0

private noncomputable def yAxisBelow (q : Point3) : Finset Point3 :=
  (Finset.range (q.y + 1)).image fun i => Point3.mk 0 i 0

private noncomputable def zAxisBelow (q : Point3) : Finset Point3 :=
  (Finset.range (q.z + 1)).image fun i => Point3.mk 0 0 i

private theorem card_xAxisBelow (q : Point3) : (xAxisBelow q).card = q.x + 1 := by
  classical
  unfold xAxisBelow
  rw [Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    exact congrArg Point3.x hab

private theorem card_yAxisBelow (q : Point3) : (yAxisBelow q).card = q.y + 1 := by
  classical
  unfold yAxisBelow
  rw [Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    exact congrArg Point3.y hab

private theorem card_zAxisBelow (q : Point3) : (zAxisBelow q).card = q.z + 1 := by
  classical
  unfold zAxisBelow
  rw [Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    exact congrArg Point3.z hab

/-- Every first coordinate occurring in the standard staircase is below its cardinality. -/
theorem standardPoint_x_lt_m (S : CyclicStaircase) {q : Point3} (hq : q ∈ S.D) :
    q.x < S.m := by
  classical
  have hsub : xAxisBelow q ⊆ S.D := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    apply S.down_closed.mem_of_le (b := q) ?_ hq
    simp only [Finset.mem_range] at hi
    change i ≤ q.x ∧ 0 ≤ q.y ∧ 0 ≤ q.z
    exact ⟨by omega, by omega, by omega⟩
  have hc := Finset.card_le_card hsub
  rw [card_xAxisBelow, S.card_D] at hc
  omega

/-- Every second coordinate occurring in the standard staircase is below its cardinality. -/
theorem standardPoint_y_lt_m (S : CyclicStaircase) {q : Point3} (hq : q ∈ S.D) :
    q.y < S.m := by
  classical
  have hsub : yAxisBelow q ⊆ S.D := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    apply S.down_closed.mem_of_le (b := q) ?_ hq
    simp only [Finset.mem_range] at hi
    change 0 ≤ q.x ∧ i ≤ q.y ∧ 0 ≤ q.z
    exact ⟨by omega, by omega, by omega⟩
  have hc := Finset.card_le_card hsub
  rw [card_yAxisBelow, S.card_D] at hc
  omega

/-- Every third coordinate occurring in the standard staircase is below its cardinality. -/
theorem standardPoint_z_lt_m (S : CyclicStaircase) {q : Point3} (hq : q ∈ S.D) :
    q.z < S.m := by
  classical
  have hsub : zAxisBelow q ⊆ S.D := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨i, hi, rfl⟩
    apply S.down_closed.mem_of_le (b := q) ?_ hq
    simp only [Finset.mem_range] at hi
    change 0 ≤ q.x ∧ 0 ≤ q.y ∧ i ≤ q.z
    exact ⟨by omega, by omega, by omega⟩
  have hc := Finset.card_le_card hsub
  rw [card_zAxisBelow, S.card_D] at hc
  omega

theorem fullSupport_minimalComplement_x_le_m (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) : g.x ≤ S.m := by
  have hp := standardPoint_x_lt_m S (hg.pred1_mem hfull.1)
  simp only [Point3.pred1_x] at hp
  omega

theorem fullSupport_minimalComplement_y_le_m (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) : g.y ≤ S.m := by
  have hp := standardPoint_y_lt_m S (hg.pred2_mem hfull.2.1)
  simp only [Point3.pred2_y] at hp
  omega

theorem fullSupport_minimalComplement_z_le_m (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) : g.z ≤ S.m := by
  have hp := standardPoint_z_lt_m S (hg.pred3_mem hfull.2.2)
  simp only [Point3.pred3_z] at hp
  omega

/-- A strict ordered full-support failure belongs to the derived 203-tuple set. -/
theorem fullSupport_strictFailure_mem_criticalResidual (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hstrict : S.m < fullTarget S) :
    FullResidualTuple.mk
      (pair12Count S.D) (pair13Count S.D) (pair23Count S.D) ∈
        criticalResidualTupleFinset := by
  rw [mem_criticalResidualTupleFinset]
  refine ⟨fullSupport_counterexample_mem_residual S hg hfull hord (by omega), ?_⟩
  have haccount := full_resource_accounting S hg hfull
  have hM : fullM S ≤ fullTarget S := by omega
  have hsq := fullDeficit_square_bound S hM
  constructor
  · simpa [FullResidualTuple.largeStripArithmetic, fullResidualM, fullM,
      fullTarget] using hM
  · simpa using hsq

/-- Strict failure plus the 307 target cap forces `m ≤ 306`. -/
theorem fullSupport_strictFailure_m_le_306 (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hstrict : S.m < fullTarget S) : S.m ≤ 306 := by
  have hmem := fullSupport_strictFailure_mem_criticalResidual S hg hfull hord hstrict
  have htarget := criticalResidualTuple_target_le hmem
  change fullTarget S ≤ 307 at htarget
  omega

/-- Every strict ordered full-support failure maps into the exact 4013-state envelope. -/
theorem fullSupport_strictFailure_mem_arithmeticState (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hstrict : S.m < fullTarget S) :
    (FullResidualTuple.mk
      (pair12Count S.D) (pair13Count S.D) (pair23Count S.D), S.m) ∈
        strictFailureArithmeticStateFinset := by
  rw [mem_strictFailureArithmeticStateFinset]
  refine ⟨fullSupport_strictFailure_mem_criticalResidual S hg hfull hord hstrict, ?_, ?_⟩
  · have haccount := full_resource_accounting S hg hfull
    simpa [fullResidualM, fullM] using
      (show fullM S ≤ S.m by omega)
  · simpa [fullTarget] using hstrict

end NSP3
