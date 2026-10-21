import NSP3.CertifiedCoverRows
import NSP3.FastReducedClassifier

namespace NSP3

set_option maxRecDepth 1000000
set_option maxHeartbeats 400000000

instance {m : ℕ} (row : CertificateRow) (q : FullResidualTuple)
    (g : Point3) (w : ResidueWeights m) : Decidable (certificateRowMatches row q g w) := by
  unfold certificateRowMatches
  infer_instance

/-- An exact source-equivalent slice classifier, not a test of row counts. -/
def sliceRowCheck (q : FullResidualTuple) (m : ℕ) : Bool :=
  if hm : m = 0 then true else
    letI : NeZero m := ⟨hm⟩
    decide (fullResidualM q.r q.s q.t ≤ m →
      ∀ g ∈ productBoundaries m, fastSeedFeasible q m g →
        ∀ w ∈ fastReducedWeightCandidates q m g,
          ∃ row ∈ checkedCertificateRows, certificateRowMatches row q g w)

def sliceChecked (q : FullResidualTuple) : Bool :=
  (List.range (quarterSquareCeil (q.r+q.s+q.t+2))).all (sliceRowCheck q)

theorem sliceChecked_covers (q : FullResidualTuple) (h : sliceChecked q = true)
    (m : ℕ) [NeZero m] (g : Point3) (w : ResidueWeights m)
    (hr : ReducedCheckerState q m g w) :
    ∃ row ∈ checkedCertificateRows, certificateRowMatches row q g w := by
  have hb := (mem_strictFailureArithmeticStateFinset _).mp hr.1.1
  have hm : m ∈ List.range (quarterSquareCeil (q.r+q.s+q.t+2)) :=
    List.mem_range.mpr hb.2.2
  have hc : sliceRowCheck q m = true := (List.all_eq_true.mp h) m hm
  simp only [sliceRowCheck,dif_neg (NeZero.ne m)] at hc
  have hs := of_decide_eq_true hc
  have hf := (reducedState_fast_iff q g w).mp hr
  exact hs hb.2.1 g
    ((mem_productBoundaries m g).mpr ⟨hr.2.1.1,hr.2.1.2.2.2⟩)
    hf.2.2.1 w hf.2.2.2

/-- A checked slice excludes every original completion for that q, without any
global table-coverage assumption. -/
theorem no_terminal_of_sliceChecked (q : FullResidualTuple)
    (hs : sliceChecked q = true) (m : ℕ) [NeZero m]
    (g : Point3) (w : ResidueWeights m) (hr : ReducedCheckerState q m g w)
    (D : Finset Point3)
    (hD : D ∈ downsetCompletions (m-(mandatorySeed q g).card) m w
      (mandatorySeed q g)) : ¬ terminalMatches q m g D := by
  obtain ⟨row,hrow,hq,hme,hg,h1,h2,h3⟩ := sliceChecked_covers q hs m g w hr
  subst q
  subst m
  subst g
  have hw : certificateRowWeights row = w := by
    cases w
    simp_all [certificateRowWeights]
  rw [← hw] at hD
  exact certificateRowCheck_sound row
    ((List.all_eq_true.mp checked_certificateRows_checked) row hrow) D hD

end NSP3
