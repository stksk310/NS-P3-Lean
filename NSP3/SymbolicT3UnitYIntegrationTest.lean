import NSP3.SymbolicT3UnitYIntegration
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z)
    (hfar : pair13Count S.D+2 ≤ pair12Count S.D) : fullTarget S ≤ S.m :=
  fullSupport_t3_unit_x_far_sharp S hg hf ho ht hx hy hz hfar
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : 2 ≤ g.x) : fullTarget S ≤ S.m :=
  fullSupport_t3_x_nonunit_symbolic_sharp S hg hf ho ht hx
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) :
    fullTarget S ≤ S.m ∨
      (g.x=1 ∧ 2 ≤ g.y ∧ 2 ≤ g.z ∧ pair12Count S.D ≤ pair13Count S.D+1) ∨
      (g.x=1 ∧ 2 ≤ g.y ∧ g.z=1) ∨ (g.x=1 ∧ g.y=1 ∧ 2 ≤ g.z) :=
  fullSupport_t3_remaining_x_unit_cover S hg hf ho ht
end NSP3
