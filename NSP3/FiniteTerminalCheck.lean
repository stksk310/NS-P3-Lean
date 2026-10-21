import NSP3.FiniteCheckerCoverage

namespace NSP3

instance minimalComplementDecidable (D : Finset Point3) (b : Point3) :
    Decidable (MinimalComplement D b) := by
  unfold MinimalComplement
  infer_instance

instance fullSupportDecidable (b : Point3) : Decidable (FullSupport b) := by
  unfold FullSupport
  infer_instance

instance pair12Decidable (b : Point3) : Decidable (Pair12 b) := by
  unfold Pair12
  infer_instance

instance pair13Decidable (b : Point3) : Decidable (Pair13 b) := by
  unfold Pair13
  infer_instance

instance pair23Decidable (b : Point3) : Decidable (Pair23 b) := by
  unfold Pair23
  infer_instance

def checkerPair12Boundaries (D : Finset Point3) : Finset Point3 :=
  (D.image fun p => p + Point3.e1).filter fun b =>
    MinimalComplement D b ∧ Pair12 b

def checkerPair13Boundaries (D : Finset Point3) : Finset Point3 :=
  (D.image fun p => p + Point3.e1).filter fun b =>
    MinimalComplement D b ∧ Pair13 b

def checkerPair23Boundaries (D : Finset Point3) : Finset Point3 :=
  (D.image fun p => p + Point3.e2).filter fun b =>
    MinimalComplement D b ∧ Pair23 b

def checkerPair12Count (D : Finset Point3) : ℕ :=
  (checkerPair12Boundaries D).card

def checkerPair13Count (D : Finset Point3) : ℕ :=
  (checkerPair13Boundaries D).card

def checkerPair23Count (D : Finset Point3) : ℕ :=
  (checkerPair23Boundaries D).card

theorem checkerPair12Boundaries_eq (D : Finset Point3) :
    checkerPair12Boundaries D = pair12Boundaries D := by
  classical
  ext b
  simp only [checkerPair12Boundaries, Finset.mem_filter,
    mem_pair12Boundaries]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    exact Finset.mem_image.mpr
      ⟨b.pred1, h.1.pred1_mem h.2.1, b.pred1_add_e1 h.2.1⟩

theorem checkerPair13Boundaries_eq (D : Finset Point3) :
    checkerPair13Boundaries D = pair13Boundaries D := by
  classical
  ext b
  simp only [checkerPair13Boundaries, Finset.mem_filter,
    mem_pair13Boundaries]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    exact Finset.mem_image.mpr
      ⟨b.pred1, h.1.pred1_mem h.2.1, b.pred1_add_e1 h.2.1⟩

theorem checkerPair23Boundaries_eq (D : Finset Point3) :
    checkerPair23Boundaries D = pair23Boundaries D := by
  classical
  ext b
  simp only [checkerPair23Boundaries, Finset.mem_filter,
    mem_pair23Boundaries]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    exact Finset.mem_image.mpr
      ⟨b.pred2, h.1.pred2_mem h.2.2.1, b.pred2_add_e2 h.2.2.1⟩

theorem checkerPair12Count_eq (D : Finset Point3) :
    checkerPair12Count D = pair12Count D := by
  simp [checkerPair12Count, pair12Count, checkerPair12Boundaries_eq]

theorem checkerPair13Count_eq (D : Finset Point3) :
    checkerPair13Count D = pair13Count D := by
  simp [checkerPair13Count, pair13Count, checkerPair13Boundaries_eq]

theorem checkerPair23Count_eq (D : Finset Point3) :
    checkerPair23Count D = pair23Count D := by
  simp [checkerPair23Count, pair23Count, checkerPair23Boundaries_eq]

/-- Canonical terminal recomputation; no pair count or boundary property is
trusted from the input labels. -/
def terminalMatches (q : FullResidualTuple) (m : ℕ) (g : Point3)
    (D : Finset Point3) : Prop :=
  D.card = m ∧ MinimalComplement D g ∧ FullSupport g ∧
    checkerPair12Count D = q.r ∧ checkerPair13Count D = q.s ∧
    checkerPair23Count D = q.t

instance (q : FullResidualTuple) (m : ℕ) (g : Point3) (D : Finset Point3) :
    Decidable (terminalMatches q m g D) := by
  unfold terminalMatches
  infer_instance

theorem actual_standardSet_terminalMatches (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    terminalMatches
      (FullResidualTuple.mk (pair12Count S.D) (pair13Count S.D)
        (pair23Count S.D)) S.m g S.D := by
  unfold terminalMatches
  exact ⟨S.card_D, hg, hfull, checkerPair12Count_eq S.D,
    checkerPair13Count_eq S.D, checkerPair23Count_eq S.D⟩

end NSP3
