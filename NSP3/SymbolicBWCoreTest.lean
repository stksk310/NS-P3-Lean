import NSP3.SymbolicBWCore

namespace NSP3

example (S : CyclicStaircase) :
    (fullCoreFinset S).card =
      ∑ y ∈ Finset.Icc 1 (pair23Count S.D),
      ∑ z ∈ Finset.Icc 1 (pair23Count S.D),
        if y+z ≤ pair23Count S.D then
          min (pair12Count S.D-y) (pair13Count S.D-z) else 0 := by
  exact fullCore_card_eq_coreCardRows S

example (S : CyclicStaircase) (g : Point3) :
    fullSupportSymbolicBW S g ≤ fullSupportSymbolicBF S g := by
  exact fullSupportSymbolicBW_le_BF S g

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    1+3*pair12Count S.D+Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+Nat.choose (pair23Count S.D) 2+
      max (g.x*g.y*g.z-1) ((fullCoreFinset S).card-largeHoleCap (pair23Count S.D))+
      ferrersPlaneDefect (pair12Count S.D) g.x g.y+
      ferrersPlaneDefect (pair13Count S.D) g.x g.z+
      ferrersPlaneDefect (pair23Count S.D) g.y g.z ≤ fullSupportSymbolicBW S g := by
  exact fullSupport_symbolic_BW_core_box_lower S hg hf ho

end NSP3
