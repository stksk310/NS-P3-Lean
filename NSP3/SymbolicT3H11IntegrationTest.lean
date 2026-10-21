import NSP3.SymbolicT3H11Integration

namespace NSP3
example (r s h : ℤ) :
    2*r*(r-1)+2*s*(s-1)+4*r+4*s+16*h+16-(r+s+5)^2=
      (r-s-1)*(r-s+9)+16*(h-r) := t3_h11_polynomial_identity r s h

-- Height is deliberately NOT a premise: actual terminal capacity must supply it.
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : 4≤pair12Count S.D) (hy : g.y=1) (hz : g.z=1) : fullTarget S≤S.m :=
  fullSupport_t3_h11_ge4_sharp S hg hf ho ht hr hy hz
end NSP3
