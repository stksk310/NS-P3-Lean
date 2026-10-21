import NSP3.CoverDAGCertificate
namespace NSP3
#check coverDAGCheck_sound

private def terminalControl : Finset Point3 :=
  (fastSeedLowerBox ⟨1,1,1⟩).erase ⟨1,1,1⟩
private def rootControl : CoverDAGNode := ⟨{Point3.zero},1⟩
private def childControl : CoverDAGNode := ⟨{Point3.zero,Point3.e1},0⟩

example : terminalMatches ⟨0,0,0⟩ 7 ⟨1,1,1⟩ terminalControl := by decide
example : coverDAGCheck ⟨0,0,0⟩ ⟨1,1,1⟩ (⟨1,2,4⟩ : ResidueWeights 7)
    terminalControl [⟨terminalControl,0⟩] = false := by decide
-- Wrong pair counts can close a leaf, but not the legitimate terminal query.
example : coverDAGCheck ⟨1,0,0⟩ ⟨1,1,1⟩ (⟨1,2,4⟩ : ResidueWeights 7)
    terminalControl [⟨terminalControl,0⟩] = true := by decide
-- The complete two-point universe has one required branch for residue 1.
example : coverDAGCheck ⟨0,0,0⟩ ⟨1,1,1⟩ (⟨1,0,0⟩ : ResidueWeights 2)
    {Point3.zero,Point3.e1} [rootControl,childControl] = true := by decide
example : coverDAGCheck ⟨0,0,0⟩ ⟨1,1,1⟩ (⟨1,0,0⟩ : ResidueWeights 2)
    {Point3.zero,Point3.e1} [rootControl] = false := by decide
example : coverDAGCheck ⟨0,0,0⟩ ⟨1,1,1⟩ (⟨1,0,0⟩ : ResidueWeights 2)
    {Point3.zero,Point3.e1} [rootControl,⟨{Point3.zero,Point3.e2},0⟩] = false := by decide
example : coverDAGCheck ⟨0,0,0⟩ ⟨1,1,1⟩ (⟨1,0,0⟩ : ResidueWeights 2)
    {Point3.zero,Point3.e1} [childControl,rootControl] = false := by decide
-- A nonunit first coefficient is retained and verified without division.
example : coverDAGCheck ⟨0,0,0⟩ ⟨1,1,1⟩ (⟨3,1,2⟩ : ResidueWeights 6)
    {Point3.zero,Point3.e1} [⟨{Point3.zero},3⟩,⟨{Point3.zero,Point3.e1},1⟩] = true := by decide
example : coverDAGCheck ⟨0,0,0⟩ ⟨1,1,1⟩ (⟨3,1,2⟩ : ResidueWeights 6)
    {Point3.zero,Point3.e1} [⟨{Point3.zero},3⟩] = false := by decide
example : certificateRowDAGCheck ⟨⟨0,0,0⟩,7,⟨1,1,1⟩,1,2,4⟩
    [⟨terminalControl,0⟩] = false := by decide
example : certificateRowDAGCheck ⟨⟨0,0,0⟩,7,⟨1,1,1⟩,1,2,4⟩ [] = false := by decide
example : certificateRowDAGCheck ⟨⟨0,0,0⟩,0,⟨1,1,1⟩,0,0,0⟩ [] = false := by decide
end NSP3
