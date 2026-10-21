import NSP3.CoverageFourAtoms

namespace NSP3.Coverage

example (S : Set ℕ) (m : ℕ)
    (hfinite : {n | SemigroupAtom S n}.Finite)
    (hedim : semigroupEmbeddingDimension S = 4)
    (hm : SemigroupAtom S m) :
    ∃ a b c : ℕ, ([m,a,b,c] : List ℕ).Nodup ∧
      ∀ n, SemigroupAtom S n ↔ n ∈ ([m,a,b,c] : List ℕ) :=
  four_atoms_of_finite_edim_four S m hfinite hedim hm

#print axioms four_atoms_of_finite_edim_four

end NSP3.Coverage
