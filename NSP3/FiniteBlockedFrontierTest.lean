import NSP3.FiniteBlockedFrontier

namespace NSP3

example : (blockedPair12 (⟨1,2,0⟩ : ResidueWeights 3)
    {Point3.zero,Point3.e1,Point3.e2}).card = 1 := by decide
example : (blockedPair12 (⟨1,1,0⟩ : ResidueWeights 3)
    {Point3.zero,Point3.e1,Point3.e2}).card = 0 := by decide
example : (blockedPair13 (⟨1,0,2⟩ : ResidueWeights 3)
    {Point3.zero,Point3.e1,Point3.e3}).card = 1 := by decide
example : (blockedPair13 (⟨1,0,1⟩ : ResidueWeights 3)
    {Point3.zero,Point3.e1,Point3.e3}).card = 0 := by decide
example : (blockedPair23 (⟨0,1,2⟩ : ResidueWeights 3)
    {Point3.zero,Point3.e2,Point3.e3}).card = 1 := by decide
example : (blockedPair23 (⟨0,1,1⟩ : ResidueWeights 3)
    {Point3.zero,Point3.e2,Point3.e3}).card = 0 := by decide

-- A blocked point must remain a minimal complement in every injective extension.
example {m : ℕ} (w : ResidueWeights m) {A D : Finset Point3}
    (hsub : A ⊆ D) (hinj : residueInjectiveOn D w) {b : Point3}
    (hb : MinimalComplement A b)
    (hused : residueWithWeights w b ∈ A.image (residueWithWeights w)) :
    MinimalComplement D b :=
  blocked_minimalComplement_persists w hsub hinj hb hused

end NSP3
