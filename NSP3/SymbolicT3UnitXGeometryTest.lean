import NSP3.SymbolicT3UnitXGeometry

namespace NSP3

-- Break caught: adding finite, primitive or coefficient-unit premises.
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hx : g.x=1) : pair12Count S.D+1 ≤ g.y+g.z :=
  t3_unit_x_capacity S hg hf ho hx

-- Break caught: borrowing in Nat.sub or omitting an outside row.
example (S : CyclicStaircase) {g : Point3} (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    (fullSupportSymbolicH S g).card = g.y*g.z-1+(pair13Count S.D-2)+
      (pair13Count S.D-3)+(min (pair12Count S.D-2) (pair13Count S.D-1)-1) :=
  t3_unit_x_H_card_of_counts S ho ht hx hy hz

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    (fullSupportSymbolicH S g).card = g.y*g.z-1+(pair13Count S.D-2)+
      (pair13Count S.D-3)+(min (pair12Count S.D-2) (pair13Count S.D-1)-1) :=
  t3_unit_x_H_card S hg hf ho ht hx hy hz

-- Hand counts: punctured box3 + one outside point; two rows empty.
example (S : CyclicStaircase) {g : Point3} (ho : PairCountsOrdered S)
    (hr : pair12Count S.D=3) (hs : pair13Count S.D=3) (ht : pair23Count S.D=3)
    (hx : g.x=1) (hy : g.y=2) (hz : g.z=2) : (fullSupportSymbolicH S g).card=4 := by
  have h := t3_unit_x_H_card_of_counts S ho ht hx (by omega) (by omega)
  norm_num [hr,hs,hy,hz] at h;exact h

-- Balanced minimum is s-2, not s-1: box5 plus rows2+1+1.
example (S : CyclicStaircase) {g : Point3} (ho : PairCountsOrdered S)
    (hr : pair12Count S.D=4) (hs : pair13Count S.D=4) (ht : pair23Count S.D=3)
    (hx : g.x=1) (hy : g.y=2) (hz : g.z=3) : (fullSupportSymbolicH S g).card=9 := by
  have h := t3_unit_x_H_card_of_counts S ho ht hx (by omega) (by omega)
  norm_num [hr,hs,hy,hz] at h;exact h

-- Nonbalanced r=s+1 changes only the third outside row: box5+1+0+1.
example (S : CyclicStaircase) {g : Point3} (ho : PairCountsOrdered S)
    (hr : pair12Count S.D=4) (hs : pair13Count S.D=3) (ht : pair23Count S.D=3)
    (hx : g.x=1) (hy : g.y=2) (hz : g.z=3) : (fullSupportSymbolicH S g).card=7 := by
  have h := t3_unit_x_H_card_of_counts S ho ht hx (by omega) (by omega)
  norm_num [hr,hs,hy,hz] at h;exact h

example (S : CyclicStaircase) {g : Point3} (ho : PairCountsOrdered S)
    (hr : pair12Count S.D=5) (hs : pair13Count S.D=4) (ht : pair23Count S.D=3)
    (hx : g.x=1) (hy : g.y=2) (hz : g.z=4) : (fullSupportSymbolicH S g).card=12 := by
  have h := t3_unit_x_H_card_of_counts S ho ht hx (by omega) (by omega)
  norm_num [hr,hs,hy,hz] at h;exact h

end NSP3
