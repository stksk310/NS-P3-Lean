import NSP3.FiniteCoordinateBounds

namespace NSP3

#check standardPoint_x_lt_m
#check standardPoint_y_lt_m
#check standardPoint_z_lt_m
#check fullSupport_minimalComplement_x_le_m
#check fullSupport_minimalComplement_y_le_m
#check fullSupport_minimalComplement_z_le_m
#check fullSupport_strictFailure_mem_criticalResidual
#check fullSupport_strictFailure_m_le_306
#check fullSupport_strictFailure_mem_arithmeticState

example (S : CyclicStaircase) {q : Point3} (hq : q ∈ S.D) : q.x < S.m :=
  standardPoint_x_lt_m S hq

example (S : CyclicStaircase) {q : Point3} (hq : q ∈ S.D) : q.y < S.m :=
  standardPoint_y_lt_m S hq

example (S : CyclicStaircase) {q : Point3} (hq : q ∈ S.D) : q.z < S.m :=
  standardPoint_z_lt_m S hq

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) : g.x ≤ S.m :=
  fullSupport_minimalComplement_x_le_m S hg hfull

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hstrict : S.m < fullTarget S) : S.m ≤ 306 :=
  fullSupport_strictFailure_m_le_306 S hg hfull hord hstrict

end NSP3
