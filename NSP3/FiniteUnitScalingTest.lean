import NSP3.FiniteUnitScaling

namespace NSP3

private def u30 : (ZMod 30)ˣ := ZMod.unitOfCoprime 7 (by decide)

example : scaleResidueWeights u30 (⟨2,3,5⟩ : ResidueWeights 30) =
    (⟨14,21,5⟩ : ResidueWeights 30) := by decide

-- Three legal children, including preservation of fresh residues under scaling.
example : (extensionCandidates 4 (⟨1,2,3⟩ : ResidueWeights 4)
    {Point3.zero}).card = 3 := by decide

-- Catches failure to scale all three coefficients or to preserve all children.
example {m : ℕ} (u : (ZMod m)ˣ) (w : ResidueWeights m)
    (A : Finset Point3) (n fuel : ℕ) :
    downsetCompletions fuel n (scaleResidueWeights u w) A =
      downsetCompletions fuel n w A :=
  downsetCompletions_unit_scale u w fuel n A

example {m : ℕ} [NeZero m] (w : ResidueWeights m) (h : w.p1 ≠ 0) :
    ∃ (u : (ZMod m)ˣ) (d : ℕ), d ∣ m ∧ 0 < d ∧ d < m ∧
      (scaleResidueWeights u w).p1 = (d : ZMod m) :=
  exists_divisor_normalization w h

end NSP3
