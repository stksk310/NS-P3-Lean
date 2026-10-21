import NSP3.MinimalGeneratorClass

namespace NSP3.Coverage

/-- A finite atom set has its genuine finite cardinality as embedding dimension. -/
theorem atom_toFinset_card (S : Set ℕ)
    (hfinite : {n | SemigroupAtom S n}.Finite) :
    hfinite.toFinset.card = semigroupEmbeddingDimension S := by
  change hfinite.toFinset.card = Nat.card {n // n ∈ {n | SemigroupAtom S n}}
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfinite]

/-- Fixing one atom of a finite, four-dimensional atom set leaves three distinct atoms. -/
theorem four_atoms_of_finite_edim_four (S : Set ℕ) (m : ℕ)
    (hfinite : {n | SemigroupAtom S n}.Finite)
    (hedim : semigroupEmbeddingDimension S = 4)
    (hm : SemigroupAtom S m) :
    ∃ a b c : ℕ, ([m,a,b,c] : List ℕ).Nodup ∧
      ∀ n, SemigroupAtom S n ↔ n ∈ ([m,a,b,c] : List ℕ) := by
  classical
  let atoms := hfinite.toFinset
  have hcard : atoms.card = 4 := (atom_toFinset_card S hfinite).trans hedim
  have hmem : m ∈ atoms := by simpa [atoms] using hm
  have herase : (atoms.erase m).card = 3 := by
    rw [Finset.card_erase_of_mem hmem, hcard]
  obtain ⟨a, b, c, hab, hac, hbc, he⟩ := Finset.card_eq_three.mp herase
  have hma : m ≠ a := by
    have : a ∈ atoms.erase m := by rw [he]; simp
    exact (Finset.mem_erase.mp this).1.symm
  have hmb : m ≠ b := by
    have : b ∈ atoms.erase m := by rw [he]; simp
    exact (Finset.mem_erase.mp this).1.symm
  have hmc : m ≠ c := by
    have : c ∈ atoms.erase m := by rw [he]; simp
    exact (Finset.mem_erase.mp this).1.symm
  refine ⟨a, b, c, ?_, ?_⟩
  · simp [List.nodup_cons, hma, hmb, hmc, hab, hac, hbc]
  · intro n
    have hn : SemigroupAtom S n ↔ n ∈ atoms := by simp [atoms]
    rw [hn]
    have hrestore : insert m (atoms.erase m) = atoms := Finset.insert_erase hmem
    rw [← hrestore, he]
    simp

end NSP3.Coverage
