import NSP3.SymbolicT3TwoUnitGeometry
namespace NSP3
example (S : CyclicStaircase) (ho : PairCountsOrdered S) (ht : pair23Count S.D=3) :
    (fullCoreFinset S).card=(pair13Count S.D-1)+(pair13Count S.D-2)+
      min (pair12Count S.D-2) (pair13Count S.D-1) := t3_fullCore_card_exact S ho ht
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hu : g.y=1 ∨ g.z=1) :
    (fullSupportSymbolicH S g).card+6=g.y+g.z-1+
      2*pair13Count S.D+min (pair12Count S.D-2) (pair13Count S.D-1) :=
  t3_two_unit_H_card S hg hf ho ht hx hu
end NSP3
