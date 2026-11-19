import PaperTheorems

namespace NSP3.R18AppendixCheck

noncomputable def presentationCardinality (S : Set Nat) : Nat :=
  sInf {n : Nat | Exists fun R : Finset (Prod (AtomCoefficients S)
                                             (AtomCoefficients S)) =>
    And (IsAtomPresentation S R) (R.card = n)}

def presentationCardinalities (m : Nat) : Set Nat :=
  {n | Exists fun S : AddSubmonoid Nat =>
    And (Set.Finite (Set.compl (S : Set Nat)))
      (And (semigroupEmbeddingDimension (S : Set Nat) = 4)
        (And (IsSemigroupMultiplicity (S : Set Nat) m)
          (presentationCardinality (S : Set Nat) = n)))}

theorem max_presentation_cardinality (m : Nat) (hm : 4 <= m) :
    IsGreatest (presentationCardinalities m)
      (Nat.floor ((2 : Real) + 2 * Real.sqrt (m : Real))) :=
  NSP3.Paper.max_presentation_card_eq m hm

theorem attainable_presentation_cardinalities
    (m : Nat) (hm : 4 <= m) :
    presentationCardinalities m =
      if m = 4 then ({6} : Set Nat)
      else if m = 5 then {5, 6}
      else if m = 6 then {4, 5, 6}
      else if m = 7 then {4, 5, 6, 7}
      else Set.Icc 3 (2 + Nat.sqrt (4 * m)) :=
  NSP3.Paper.attainable_presentation_cardinalities m hm

#print axioms max_presentation_cardinality
#print axioms attainable_presentation_cardinalities
end NSP3.R18AppendixCheck
