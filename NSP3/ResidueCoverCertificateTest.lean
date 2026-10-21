import NSP3.ResidueCoverCertificate

namespace NSP3

private def positiveD : Finset Point3 :=
  (fastSeedLowerBox ⟨1,1,1⟩).erase ⟨1,1,1⟩

example : terminalMatches ⟨0,0,0⟩ 7 ⟨1,1,1⟩ positiveD := by decide
example : residueInjectiveOn positiveD (⟨1,2,4⟩ : ResidueWeights 7) := by decide
-- A real terminal must not be rejected, even with more split fuel.
example : verifyCoverReject 1 ⟨0,0,0⟩ ⟨1,1,1⟩
    (⟨1,2,4⟩ : ResidueWeights 7) positiveD positiveD = false := by decide
-- Deliberate mutations of the terminal query are rejected by recomputation.
example : verifyCoverReject 0 ⟨1,0,0⟩ ⟨1,1,1⟩
    (⟨1,2,4⟩ : ResidueWeights 7) positiveD positiveD = true := by decide
example : verifyCoverReject 0 ⟨0,0,0⟩ ⟨2,1,1⟩
    (⟨1,2,4⟩ : ResidueWeights 7) positiveD positiveD = true := by decide
example : verifyCoverReject 1 ⟨0,0,0⟩ ⟨1,1,1⟩
    (⟨0,0,0⟩ : ResidueWeights 2) {Point3.zero} {Point3.zero} = true := by decide

-- An omitted universe can pass the local verifier, but cannot meet its soundness
-- theorem's D-subset-U premise. This fixture protects that trust boundary.
example : verifyCoverReject 1 ⟨0,0,0⟩ ⟨1,1,1⟩
    (⟨1,2,4⟩ : ResidueWeights 7) ∅ {Point3.zero} = true := by decide
example : ¬ positiveD ⊆ (∅ : Finset Point3) := by decide

example {m : ℕ} [NeZero m] (fuel : ℕ) (q : FullResidualTuple)
    (g : Point3) (w : ResidueWeights m) (U A D : Finset Point3)
    (hv : coverReject fuel q g w U A) (hd : IsDownset D)
    (hs : A ⊆ D) (hu : D ⊆ U) (hi : residueInjectiveOn D w)
    (hc : D.card = m) (hg : g ∉ D) : ¬ terminalMatches q m g D :=
  coverReject_sound fuel q g w U A D hv hd hs hu hi hc hg

example {m : ℕ} [NeZero m] (fuel : ℕ) (q : FullResidualTuple)
    (g : Point3) (w : ResidueWeights m) (U A D : Finset Point3)
    (hv : coverReject fuel q g w U A) (ha : IsDownset A)
    (hi : residueInjectiveOn A w) (hau : A ⊆ U) (hbu : pointBox m ⊆ U)
    (hD : D ∈ downsetCompletions fuel m w A) : ¬ terminalMatches q m g D :=
  coverReject_excludes_completions fuel q g w U A D hv ha hi hau hbu hD

example (h : GlobalCoverCertificates) : ReducedNoTarget :=
  reducedNoTarget_of_globalCoverCertificates h

end NSP3
