import NSP3.SymbolicJointAxes
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) :
    fullSupportAxisGain S g ≤
      (pure1Intercept S-1-max (pair12Count S.D) g.x)+
      (pure2Intercept S-1-max (pair12Count S.D) g.y)+
      (pure3Intercept S-1-max (pair12Count S.D) g.z) :=
    fullSupport_joint_axis_pressure S hg hf ho
end NSP3
