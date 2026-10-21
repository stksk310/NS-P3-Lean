import NSP3.CoverageAtoms

namespace NSP3.Coverage

example (S : AddSubmonoid ℕ) (hcof : ((S : Set ℕ)ᶜ).Finite) :
    ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ, C ≤ n → n ∈ S := cofinite_tail S hcof

example (S : AddSubmonoid ℕ) (m : ℕ)
    (hm : IsSemigroupMultiplicity (S : Set ℕ) m) :
    SemigroupAtom (S : Set ℕ) m := multiplicity_atom S hm

example (S : AddSubmonoid ℕ) (m : ℕ)
    (hcof : ((S : Set ℕ)ᶜ).Finite)
    (hm : IsSemigroupMultiplicity (S : Set ℕ) m) :
    {n : ℕ | SemigroupAtom (S : Set ℕ) n}.Finite := atoms_finite S hcof hm

example (S T : AddSubmonoid ℕ)
    (h : ∀ n : ℕ, SemigroupAtom (S : Set ℕ) n → n ∈ T) : S ≤ T :=
  atoms_generate S T h

example (S : AddSubmonoid ℕ) (hcof : ((S : Set ℕ)ᶜ).Finite) :
    {n : ℕ | SemigroupAtom (S : Set ℕ) n}.Finite :=
  atoms_finite_of_cofinite S hcof

-- The zero-only submonoid is included in the generation theorem.
example (T : AddSubmonoid ℕ) : (⊥ : AddSubmonoid ℕ) ≤ T := by
  apply atoms_generate
  intro n hn
  have hz : n = 0 := by simpa using hn.1
  have hp : 0 < n := hn.2.1
  exact False.elim (by omega)

end NSP3.Coverage


