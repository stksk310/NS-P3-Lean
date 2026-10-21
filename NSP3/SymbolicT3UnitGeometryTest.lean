import NSP3.SymbolicT3UnitGeometry

namespace NSP3

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hz : g.z = 1) : pair12Count S.D + 1 ≤ g.x + g.y :=
  t3_unit_z_capacity S hg hf ho hz

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hz : g.z = 1) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) :
    (fullSupportSymbolicH S g).card =
      g.x * g.y + pair13Count S.D - 3 + (pair13Count S.D - 1 - g.x) +
        (min (pair12Count S.D - 2) (pair13Count S.D - 1) - g.x) :=
  t3_unit_z_H_card S hg hf ho ht hz hx hy

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) :
    (2 ≤ g.x ∧ 2 ≤ g.y ∧ 2 ≤ g.z) ∨
    (2 ≤ g.x ∧ g.y = 1 ∧ g.z = 1) ∨
    (g.x = 1 ∧ 2 ≤ g.y ∧ g.z = 1) ∨
    (g.x = 1 ∧ g.y = 1 ∧ 2 ≤ g.z) ∨
    (2 ≤ g.x ∧ 2 ≤ g.y ∧ g.z = 1) ∨
    (2 ≤ g.x ∧ g.y = 1 ∧ 2 ≤ g.z) ∨
    (g.x = 1 ∧ 2 ≤ g.y ∧ 2 ≤ g.z) :=
  fullSupport_t3_unit_partition S hg hf ho ht

end NSP3
