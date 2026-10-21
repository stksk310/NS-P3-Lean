import NSP3.CertifiedSliceCoverage

namespace NSP3

set_option maxRecDepth 1000000

/-- Exact slice classifier parameterized by a separately verified row list.
No unit quotient or externally asserted survivor count enters this predicate. -/
def indexedSliceRowCheck (rows : List CertificateRow) (q : FullResidualTuple)
    (m : ℕ) : Bool :=
  if hm : m = 0 then true else
    letI : NeZero m := ⟨hm⟩
    decide (fullResidualM q.r q.s q.t ≤ m →
      ∀ g ∈ productBoundaries m, fastSeedFeasible q m g →
        ∀ w ∈ fastReducedWeightCandidates q m g,
          ∃ row ∈ rows, certificateRowMatches row q g w)

def indexedSliceChecked (rows : List CertificateRow) (q : FullResidualTuple) : Bool :=
  (List.range (quarterSquareCeil (q.r+q.s+q.t+2))).all (indexedSliceRowCheck rows q)

theorem indexedSliceChecked_covers (rows : List CertificateRow) (q : FullResidualTuple)
    (h : indexedSliceChecked rows q = true) (m : ℕ) [NeZero m]
    (g : Point3) (w : ResidueWeights m) (hr : ReducedCheckerState q m g w) :
    ∃ row ∈ rows, certificateRowMatches row q g w := by
  have hb := (mem_strictFailureArithmeticStateFinset _).mp hr.1.1
  have hm : m ∈ List.range (quarterSquareCeil (q.r+q.s+q.t+2)) :=
    List.mem_range.mpr hb.2.2
  have hc : indexedSliceRowCheck rows q m = true := (List.all_eq_true.mp h) m hm
  simp only [indexedSliceRowCheck,dite_eq_right (NeZero.ne m)] at hc
  have hf := (reducedState_fast_iff q g w).mp hr
  exact (of_decide_eq_true hc) hb.2.1 g
    ((mem_productBoundaries m g).mpr ⟨hr.2.1.1,hr.2.1.2.2.2⟩)
    hf.2.2.1 w hf.2.2.2

theorem no_terminal_of_indexedSliceChecked (rows : List CertificateRow)
    (hchecks : ∀ row ∈ rows, certificateRowCheck row = true)
    (q : FullResidualTuple) (hs : indexedSliceChecked rows q = true)
    (m : ℕ) [NeZero m] (g : Point3) (w : ResidueWeights m)
    (hr : ReducedCheckerState q m g w) (D : Finset Point3)
    (hD : D ∈ downsetCompletions (m-(mandatorySeed q g).card) m w
      (mandatorySeed q g)) : ¬ terminalMatches q m g D := by
  obtain ⟨row,hrow,hq,hme,hg,h1,h2,h3⟩ :=
    indexedSliceChecked_covers rows q hs m g w hr
  subst q
  subst m
  subst g
  have hw : certificateRowWeights row = w := by
    cases w
    simp_all [certificateRowWeights]
  rw [← hw] at hD
  exact certificateRowCheck_sound row (hchecks row hrow) D hD

end NSP3
