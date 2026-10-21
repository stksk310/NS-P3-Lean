import NSP3.SymbolicT3UnitYSharp
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=2) (hy : g.y=1) (hz : g.z=2) : fullTarget S ≤ S.m :=
  fullSupport_t3_unit_y_r3_sharp S hg hf ho ht hr hx hy hz
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z) :
    fullTarget S ≤ S.m := fullSupport_t3_one_unit_y_symbolic_sharp S hg hf ho ht hy hx hz
end NSP3
