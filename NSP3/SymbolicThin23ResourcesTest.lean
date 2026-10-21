import NSP3.SymbolicThin23Resources
namespace NSP3
-- Mutation caught: dropping the joint payment or double-counting full support.
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hs : 2 ≤ pair13Count S.D) (hy : g.y=1) (hz : g.z=1) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      4*g.x+pair12Count S.D+3 ≤ S.m :=
  fullSupport_t2_h11_lower S hg hf ho ht hs hy hz
#check long_face_axis_joint_unit
end NSP3
