import NSP3.SymbolicT3NonbalancedH11

namespace NSP3

-- Contract: removing any actual row or weakening its length must fail this type.
example (S : CyclicStaircase) {g : Point3}
    (ht : pair23Count S.D=3) (hs : 3≤pair13Count S.D)
    (hr : pair13Count S.D<pair12Count S.D) (hh : pair12Count S.D≤g.x)
    (hy : g.y=1) (hz : g.z=1) :
    g.x+2*pair13Count S.D-4≤(fullSupportSymbolicH S g).card :=
  t3_nonbalanced_h11_H_lower S ht hs hr hh hy hz

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : pair13Count S.D<pair12Count S.D) (hh : pair12Count S.D≤g.x)
    (hy : g.y=1) (hz : g.z=1) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      pair12Count S.D+pair13Count S.D+4*g.x+4≤S.m :=
  fullSupport_t3_nonbalanced_h11_lower S hg hf ho ht hr hh hy hz

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : pair13Count S.D<pair12Count S.D) (hh : pair12Count S.D≤g.x)
    (hy : g.y=1) (hz : g.z=1) : fullTarget S≤S.m :=
  fullSupport_t3_nonbalanced_h11_sharp S hg hf ho ht hr hh hy hz

end NSP3
