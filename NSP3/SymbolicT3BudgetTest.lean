import NSP3.SymbolicT3Budget
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (ht : pair23Count S.D=3) (he : pair12Count S.D=pair13Count S.D)
    (hk : 4≤pair12Count S.D) (hh : g.x=pair12Count S.D) :
    3*pair12Count S.D-5≤(fullSupportSymbolicH S g).card :=
  t3_equal_height_H_lower S ht he hk hh
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (he : pair12Count S.D=pair13Count S.D) (hk : 5≤pair12Count S.D)
    (hh : g.x=pair12Count S.D) (hy : g.y=1) (hz : g.z=1)
    (h13 : Point3.mk 0 1 3∈S.D) (h31 : Point3.mk 0 3 1∈S.D) : fullTarget S≤S.m :=
  t3_balanced_present_ge5_sharp S hg hf ho ht he hk hh hy hz h13 h31
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (he : pair12Count S.D=pair13Count S.D) (hk : 4≤pair12Count S.D)
    (hh : g.x=pair12Count S.D) (hy : g.y=1) (hz : g.z=1)
    (hnot : Point3.mk 0 1 3∉S.D ∨ Point3.mk 0 3 1∉S.D) : fullTarget S≤S.m :=
  t3_balanced_missing_sharp S hg hf ho ht he hk hh hy hz hnot
end NSP3
