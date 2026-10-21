import NSP3.CompactCoverPoints

namespace NSP3

structure CertificateRow where
  q : FullResidualTuple
  m : ℕ
  g : Point3
  p1 : ℕ
  p2 : ℕ
  p3 : ℕ
deriving DecidableEq, Repr

def certificateRowWeights (row : CertificateRow) : ResidueWeights row.m :=
  ⟨(row.p1 : ZMod row.m),(row.p2 : ZMod row.m),(row.p3 : ZMod row.m)⟩

def certificateRowCheck (row : CertificateRow) : Bool :=
  if hm : row.m = 0 then false else
    letI : NeZero row.m := ⟨hm⟩
    let A := fastMandatorySeed row.q row.g
    let w := certificateRowWeights row
    decide (residueInjectiveOn A w ∧ coverReject (row.m - A.card) row.q row.g w
      (compactCoverPoints w A row.g) A)

theorem certificateRowCheck_sound (row : CertificateRow) [NeZero row.m]
    (h : certificateRowCheck row = true) (D : Finset Point3)
    (hD : D ∈ downsetCompletions
      (row.m - (mandatorySeed row.q row.g).card) row.m
      (certificateRowWeights row) (mandatorySeed row.q row.g)) :
    ¬ terminalMatches row.q row.m row.g D := by
  simp only [certificateRowCheck,dif_neg (NeZero.ne row.m)] at h
  have hv := of_decide_eq_true h
  rw [fastMandatorySeed_eq] at hv
  exact compactCoverReject_excludes_completions _ row.q row.g
    (certificateRowWeights row) _ D (mandatorySeed_isDownset row.q row.g) hv.1 hv.2 hD

def certificateRowMatches {m : ℕ} (row : CertificateRow)
    (q : FullResidualTuple) (g : Point3) (w : ResidueWeights m) : Prop :=
  row.q = q ∧ row.m = m ∧ row.g = g ∧
    (row.p1 : ZMod m) = w.p1 ∧ (row.p2 : ZMod m) = w.p2 ∧ (row.p3 : ZMod m) = w.p3

/-- This coverage obligation must be proved separately from checking the rows.
It explicitly quantifies all reduced states, not just the external survivors. -/
def RowCoverage (rows : List CertificateRow) : Prop :=
  ∀ (q : FullResidualTuple) (m : ℕ) [NeZero m] (g : Point3) (w : ResidueWeights m),
    ReducedCheckerState q m g w → ∃ row ∈ rows, certificateRowMatches row q g w

theorem reducedNoTarget_of_checkedRows (rows : List CertificateRow)
    (hchecks : ∀ row ∈ rows, certificateRowCheck row = true)
    (hcoverage : RowCoverage rows) : ReducedNoTarget := by
  intro q m hm g w hr D hD
  obtain ⟨row,hrow,hq,hme,hg,h1,h2,h3⟩ := hcoverage q m g w hr
  subst q
  subst m
  subst g
  have hw : certificateRowWeights row = w := by
    cases w
    simp_all [certificateRowWeights]
  rw [← hw] at hD
  exact certificateRowCheck_sound row (hchecks row hrow) D hD

end NSP3
