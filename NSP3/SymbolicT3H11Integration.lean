import NSP3.SymbolicT3NonbalancedH11

namespace NSP3

/-- Four times the h11 resource polynomial minus the sharp square, over Z. -/
theorem t3_h11_polynomial_identity (r s h : ℤ) :
    2*r*(r-1)+2*s*(s-1)+4*r+4*s+16*h+16-(r+s+5)^2=
      (r-s-1)*(r-s+9)+16*(h-r) := by ring

/-- No height premise: actual terminal capacity supplies h>=r. -/
theorem fullSupport_t3_h11_ge4_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : 4≤pair12Count S.D) (hy : g.y=1) (hz : g.z=1) : fullTarget S≤S.m := by
  have hc:=pair12_terminal_return_capacity_ordered S hg hf ho
  have hh : pair12Count S.D≤g.x:=by omega
  by_cases he : pair12Count S.D=pair13Count S.D
  · exact fullSupport_t3_balanced_h11_sharp S hg hf ho ht he hr hh hy hz
  · exact fullSupport_t3_nonbalanced_h11_sharp S hg hf ho ht (by have:=ho.2;omega) hh hy hz

end NSP3
