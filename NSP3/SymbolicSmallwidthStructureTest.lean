import NSP3.SymbolicSmallwidthStructure

namespace NSP3

example (S : CyclicStaircase) (hs : 4 ≤ pair13Count S.D)
    (hr : pair13Count S.D ≤ pair12Count S.D) (ht : pair23Count S.D=4) :
    6*pair13Count S.D = (fullCoreFinset S).card+
      (if pair12Count S.D=pair13Count S.D then 13
       else if pair12Count S.D=pair13Count S.D+1 then 11 else 10) :=
  fullCore_t4_card S hs hr ht

example (S : CyclicStaircase) (hs : 4 ≤ pair13Count S.D)
    (hr : pair13Count S.D ≤ pair12Count S.D) (ht : pair23Count S.D=4) :
    6*pair13Count S.D ≤ (fullCoreFinset S).card+13 :=
  fullCore_t4_linear_lower S hs hr ht

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : pair23Count S.D=4) :
    6*pair13Count S.D ≤ (fullSupportSymbolicH S g).card+14 :=
  fullSupport_H_t4_core_lower S hg hf ho ht

example (S : CyclicStaircase) (g : Point3) :
    fullSupportSymbolicBF S g =
      1+max (pair12Count S.D) g.x+max (pair12Count S.D) g.y+
      max (pair12Count S.D) g.z+(fullSupportSymbolicH S g).card+
      Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      Nat.choose (pair23Count S.D) 2+
      max (ferrersPlaneDefect (pair12Count S.D) g.x g.y) (rankCutPhi (pair12Count S.D) g.x g.y)+
      max (ferrersPlaneDefect (pair13Count S.D) g.x g.z) (rankCutPhi (pair13Count S.D) g.x g.z)+
      max (ferrersPlaneDefect (pair23Count S.D) g.y g.z) (rankCutPhi (pair23Count S.D) g.y g.z)+
      fullSupportAxisGain S g := fullSupportSymbolicBF_eq_weighted S g

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) :
    1+3*pair12Count S.D+Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+Nat.choose (pair23Count S.D) 2+
      max (g.x*g.y*g.z-1) ((fullCoreFinset S).card-largeHoleCap (pair23Count S.D))+
      max (ferrersPlaneDefect (pair12Count S.D) g.x g.y) (rankCutPhi (pair12Count S.D) g.x g.y)+
      max (ferrersPlaneDefect (pair13Count S.D) g.x g.z) (rankCutPhi (pair13Count S.D) g.x g.z)+
      max (ferrersPlaneDefect (pair23Count S.D) g.y g.z) (rankCutPhi (pair23Count S.D) g.y g.z)+
      fullSupportAxisGain S g ≤ fullSupportSymbolicBF S g :=
  fullSupport_symbolic_BF_core_box_lower S hg hf ho

end NSP3
