import NSP3.SymbolicT3UnitXEndpoint
import NSP3.SymbolicT3UnitSharp

namespace NSP3

-- Break caught: double-counting Φ/joint gains or assuming any weight is a unit.
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=1) (hy : g.y=2) (hz : g.z=2) : 30 ≤ S.m :=
  fullSupport_t3_unit_x_r3_BF_lower S hg hf ho ht hr hx hy hz

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=1) (hy : g.y=2) (hz : g.z=2) : fullTarget S ≤ S.m :=
  fullSupport_t3_unit_x_r3_sharp S hg hf ho ht hr hx hy hz

-- Exact unrestricted priority interface; rejects classifier/gcd/finite-m premises.
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    fullTarget S ≤ S.m :=
  fullSupport_t3_one_unit_x_symbolic_sharp S hg hf ho ht hx hy hz

end NSP3
