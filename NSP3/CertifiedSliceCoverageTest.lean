import NSP3.CertifiedSlice222

namespace NSP3

example : sliceChecked ⟨2,2,2⟩ = true := slice222_checked

example (m : ℕ) [NeZero m] (g : Point3) (w : ResidueWeights m)
    (hr : ReducedCheckerState ⟨2,2,2⟩ m g w) (D : Finset Point3)
    (hD : D ∈ downsetCompletions (m-(mandatorySeed ⟨2,2,2⟩ g).card) m w
      (mandatorySeed ⟨2,2,2⟩ g)) : ¬ terminalMatches ⟨2,2,2⟩ m g D :=
  no_terminal_of_sliceChecked _ slice222_checked m g w hr D hD

end NSP3
