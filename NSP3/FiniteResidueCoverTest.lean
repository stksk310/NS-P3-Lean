import NSP3.FiniteResidueCover
namespace NSP3

-- Missing-residue rejection: all-zero weights cannot represent residue one.
example : ∀ p ∈ admissibleCoverPoints 2 (⟨0,0,0⟩ : ResidueWeights 2)
    {Point3.zero} ⟨1,1,1⟩, residueWithWeights (⟨0,0,0⟩ : ResidueWeights 2) p ≠ 1 := by
  decide

-- Negative control: residue one is available when e1 has weight one.
example : Point3.e1 ∈ admissibleCoverPoints 2 (⟨1,0,0⟩ : ResidueWeights 2)
    {Point3.zero} ⟨1,1,1⟩ := by decide
example : residueWithWeights (⟨1,0,0⟩ : ResidueWeights 2) Point3.e1 = 1 := by decide

-- Reject a branch only when a residue cannot occur in any admissible extension.
example {m : ℕ} [NeZero m] (w : ResidueWeights m) {A D : Finset Point3}
    {g : Point3} (hd : IsDownset D) (hs : A ⊆ D)
    (hb : D ⊆ pointBox m) (hi : residueInjectiveOn D w)
    (hg : g ∉ D) (hc : D.card = m) (r : ZMod m)
    (hr : ∀ p ∈ admissibleCoverPoints m w A g, residueWithWeights w p ≠ r) :
    False := no_completion_of_missing_admissible_residue w hd hs hb hi hg hc r hr

end NSP3
