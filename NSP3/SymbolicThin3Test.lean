import NSP3.SymbolicThin3
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hz : g.z=1) :
    5≤(plane23PosFinset S).card := thin23_three_corner_area_lower S hg hf ht hy hz
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hz : g.z=1)
    (he : (plane23PosFinset S).card=5) :
    Ferrers23.cornerX S 1=1 ∧ Ferrers23.cornerY S 1=4 ∧
    Ferrers23.cornerX S 2=2 ∧ Ferrers23.cornerY S 2=2 ∧
    Ferrers23.cornerX S 3=4 ∧ Ferrers23.cornerY S 3=1 :=
  thin23_three_corner_minimal_shape S hg hf ht hy hz he
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (he : pair12Count S.D=pair13Count S.D) (hk : 4≤pair12Count S.D)
    (hh : pair12Count S.D≤g.x) (hy : g.y=1) (hz : g.z=1) :
    (pair12Count S.D)^2+pair12Count S.D+4*g.x+3≤S.m :=
  fullSupport_t3_balanced_h11_lower S hg hf ho ht he hk hh hy hz
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (he : pair12Count S.D=pair13Count S.D) (hk : 4≤pair12Count S.D)
    (hh : pair12Count S.D<g.x) (hy : g.y=1) (hz : g.z=1) : fullTarget S≤S.m :=
  fullSupport_t3_balanced_h11_strict_height_sharp S hg hf ho ht he hk hh hy hz
end NSP3
