import NSP3.SymbolicT3UnitCover

namespace NSP3

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hz : g.z = 1) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) :
    fullTarget S ≤ S.m ∨
      (pair12Count S.D = 4 ∧ pair13Count S.D = 3 ∧ g.x = 2 ∧ g.y = 3) ∨
      (pair12Count S.D = pair13Count S.D ∧ pair12Count S.D ≤ 5 ∧
        g.x = pair12Count S.D-1 ∧ g.y = 2) ∨
      (pair12Count S.D = 4 ∧ pair13Count S.D = 4 ∧ g.x = 2 ∧ g.y = 3) :=
  fullSupport_t3_unit_z_symbolic_cover S hg hf ho ht hz hx hy

end NSP3
