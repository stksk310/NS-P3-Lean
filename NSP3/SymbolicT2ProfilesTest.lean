import NSP3.SymbolicT2Profiles
namespace NSP3
example (S : CyclicStaircase) (g : Point3) (hf : FullSupport g) :
    g.x*g.y*g.z-1 ≤ (fullSupportSymbolicH S g).card :=
  positive_box_H_lower S g hf
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (hx : 2≤g.x) (hy : 2≤g.y) (hz : 2≤g.z) : fullTarget S≤S.m :=
  fullSupport_t2_no_unit_sharp S hg hf ho ht hx hy hz
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2) :
    g.x=1 ∨ g.y=1 ∨ g.z=1 ∨ fullTarget S≤S.m :=
  fullSupport_t2_unit_profile_split S hg hf ho ht
end NSP3
