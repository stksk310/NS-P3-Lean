import NSP3.SymbolicT3Evidence
namespace NSP3
example (S : CyclicStaircase) (hk : pair13Count S.D=4)
    (hZ : pure3Intercept S=5) (hE : (pair13ExtraFinset S).card=1)
    (hrow : Point3.mk 4 0 1∈S.D) :
    Ferrers13.cornerX S 1=1 ∧ Ferrers13.cornerY S 1=4 ∧
    Ferrers13.cornerX S 2=2 ∧ Ferrers13.cornerY S 2=3 ∧
    Ferrers13.cornerX S 3=3 ∧ Ferrers13.cornerY S 3=2 ∧
    Ferrers13.cornerX S 4=5 ∧ Ferrers13.cornerY S 4=1 :=
  t3_k4_long13_shape S hk hZ hE hrow
example (S : CyclicStaircase) (hk : pair12Count S.D=4)
    (hY : pure2Intercept S=5) (hE : (pair12ExtraFinset S).card=1)
    (hrow : Point3.mk 4 1 0∈S.D) :
    Ferrers.cornerX S 1=1 ∧ Ferrers.cornerY S 1=4 ∧
    Ferrers.cornerX S 2=2 ∧ Ferrers.cornerY S 2=3 ∧
    Ferrers.cornerX S 3=3 ∧ Ferrers.cornerY S 3=2 ∧
    Ferrers.cornerX S 4=5 ∧ Ferrers.cornerY S 4=1 :=
  t3_k4_long12_shape S hk hY hE hrow
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (he : pair12Count S.D=pair13Count S.D)
    (hk : pair12Count S.D=4) (hh : g.x=4) (hy : g.y=1) (hz : g.z=1)
    (h13 : Point3.mk 0 1 3∈S.D) (h31 : Point3.mk 0 3 1∈S.D)
    (hm : S.m≤42) : (S.D.filter fun p=>0<p.x ∧ 0<p.y ∧ 0<p.z).card=9 :=
  t3_balanced_k4_full_support_card S hg hf ht he hk hh hy hz h13 h31 hm
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (he : pair12Count S.D=pair13Count S.D)
    (hk : pair12Count S.D=4) (hh : g.x=4) (hy : g.y=1) (hz : g.z=1)
    (h13 : Point3.mk 0 1 3∈S.D) (h31 : Point3.mk 0 3 1∈S.D)
    (hm : S.m≤42) :
    Ferrers23.cornerX S 1=1 ∧ Ferrers23.cornerY S 1=4 ∧
    Ferrers23.cornerX S 2=2 ∧ Ferrers23.cornerY S 2=2 ∧
    Ferrers23.cornerX S 3=4 ∧ Ferrers23.cornerY S 3=1 :=
  t3_balanced_k4_yz_shape S hg hf ht he hk hh hy hz h13 h31 hm
end NSP3
