import NSP3.CompactCoverPoints

namespace NSP3

example (p : Point3) : (fastSeedLowerBox p).card = (p.x+1)*(p.y+1)*(p.z+1) :=
  card_fastSeedLowerBox p
example (m : ℕ) (p : Point3) :
    p ∈ productVolumePoints m ↔ (p.x+1)*(p.y+1)*(p.z+1) ≤ m :=
  mem_productVolumePoints m p
example : Point3.mk 2 1 1 ∈ productVolumePoints 12 := by decide
example : Point3.mk 2 1 1 ∉ productVolumePoints 11 := by decide
-- Cheap freshness filter must not drop the seed itself.
example : Point3.zero ∈ compactCoverPoints (⟨1,0,0⟩ : ResidueWeights 2)
    {Point3.zero} ⟨1,1,1⟩ := by decide
example : Point3.e1 ∉ compactCoverPoints (⟨0,0,0⟩ : ResidueWeights 2)
    {Point3.zero} ⟨1,1,1⟩ := by decide

end NSP3
