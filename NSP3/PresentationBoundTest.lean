import NSP3.PresentationBound

namespace NSP3
-- Catches defining relation number as boundary card or silently assuming a presentation exists.
example (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    ∃ R : Finset (Fact4 × Fact4), IsFactorPresentation m a b c R ∧
      R.card = minimumFourInputRelations m a b c :=
  minimumFourInputRelations_attained m a b c hm hgcd

example (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    minimumFourInputRelations m a b c ≤
      Nat.card {p : Point3 // MinimalComplement (aperyStandardSet m a b c hm hgcd) p} :=
  minimal_presentation_boundary_card_bridge m a b c hm hgcd

example (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    minimumFourInputRelations m a b c ≤ 2 + Nat.sqrt (4*m) :=
  minimal_presentation_four_input_sharp m a b c hm hgcd

-- Positive m with zero or redundant input weights remains in the proved general domain.
example : minimumFourInputRelations 1 0 0 0 ≤ 4 := by
  have hs : Nat.sqrt 4 = 2 := by norm_num
  simpa only [Nat.mul_one,hs] using minimal_presentation_four_input_sharp 1 0 0 0 (by decide) (by decide)

example : minimumFourInputRelations 4 2 3 4 ≤ 2 + Nat.sqrt 16 :=
  minimal_presentation_four_input_sharp 4 2 3 4 (by decide) (by decide)

-- Total gcd one does not require any individual modular unit.
example : minimumFourInputRelations 30 6 10 15 ≤ 2 + Nat.sqrt 120 :=
  minimal_presentation_four_input_sharp 30 6 10 15 (by decide) (by decide)

-- Equal-weight lex ties produce actual relations without a positive m coefficient.
example : PresentationRel (boundaryRelations 5 1 1 1 (by decide) (by decide))
    (0,Point3.e1) (0,Point3.e3) := by
  apply (boundaryRelations_generate 5 1 1 1 (by decide) (by decide) _ _).mpr
  decide

example : aperyKey 1 1 1 Point3.e3 < aperyKey 1 1 1 Point3.e1 := by decide
end NSP3
