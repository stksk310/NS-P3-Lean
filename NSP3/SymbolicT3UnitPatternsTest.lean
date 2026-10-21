import NSP3.SymbolicT3UnitPatterns

namespace NSP3
example (S : CyclicStaircase) {g : Point3} (ht : pair23Count S.D=3)
    (hr : 4≤pair12Count S.D) (hs : pair13Count S.D=pair12Count S.D-1)
    (hx : g.x=pair12Count S.D-1) (hy : g.y=2) (hz : g.z=1) :
    3*pair12Count S.D-6≤(fullSupportSymbolicH S g).card :=
  t3_one_unit_exception_H_lower S ht hr hs hx hy hz

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : 4≤pair12Count S.D) (hs : pair13Count S.D=pair12Count S.D-1)
    (hx : g.x=pair12Count S.D-1) (hy : g.y=2) (hz : g.z=1) :
    (pair12Count S.D+2)^2+1≤S.m :=
  fullSupport_t3_one_unit_exception_lower S hg hf ho ht hr hs hx hy hz

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : 4≤pair12Count S.D) (hs : pair13Count S.D=pair12Count S.D-1)
    (hx : g.x=pair12Count S.D-1) (hy : g.y=2) (hz : g.z=1) : fullTarget S≤S.m :=
  fullSupport_t3_one_unit_exception_sharp S hg hf ho ht hr hs hx hy hz
end NSP3
