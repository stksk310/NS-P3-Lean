import NSP3.SymbolicResources
namespace NSP3
#check fullSupport_axis_resource_lower
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    1+max (pair12Count S.D) g.x+max (pair12Count S.D) g.y+
      max (pair12Count S.D) g.z+fullSupportAxisGain S g+
      Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      Nat.choose (pair23Count S.D) 2+(pair12ExtraFinset S).card+
      (pair13ExtraFinset S).card+(pair23ExtraFinset S).card+
      (puncturedFullCoreFinset S g).card+
      (lowerBoxFullOutsideCoreFinset S g).card ≤ S.m :=
  fullSupport_axis_resource_lower S hg hf ho
end NSP3
