import NSP3.SymbolicT3UnitYCover
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z)
    (he : pair12Count S.D=pair13Count S.D) :
    fullTarget S ≤ S.m ∨
      (pair12Count S.D ≤ 5 ∧ g.x=pair12Count S.D-1 ∧ g.z=2) ∨
      (pair12Count S.D=4 ∧ g.x=2 ∧ g.z=3) :=
  fullSupport_t3_unit_y_balanced_cover S hg hf ho ht hy hx hz he
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hy : g.y=1)
    (he : (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ g.x=3 ∧ g.z=2) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ g.x=4 ∧ g.z=2) ∨
      (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ g.x=2 ∧ g.z=3)) :
    fullTarget S ≤ S.m := fullSupport_t3_unit_y_small_BF_sharp S hg hf ho ht hy he
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=2) (hy : g.y=1) (hz : g.z=2) : 30 ≤ S.m :=
  fullSupport_t3_unit_y_r3_BF_lower S hg hf ho ht hr hx hy hz
end NSP3
