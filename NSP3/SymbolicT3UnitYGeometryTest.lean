import NSP3.SymbolicT3UnitYGeometry
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hy : g.y = 1) : pair12Count S.D + 1 ≤ g.x + g.z :=
  t3_unit_y_capacity S hg hf ho hy
example (S : CyclicStaircase) {g : Point3}
    (ho : PairCountsOrdered S) (ht : pair23Count S.D = 3)
    (hy : g.y = 1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z)
    (hcap : pair12Count S.D + 1 ≤ g.x + g.z) :
    (fullSupportSymbolicH S g).card = g.x*g.z-1 +
      min (pair12Count S.D-2) (pair13Count S.D-1) +
      (pair13Count S.D-1-g.x)+(pair13Count S.D-2-g.x) :=
  t3_unit_y_H_card_of_capacity S ho ht hy hx hz hcap
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hy : g.y = 1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z) :
    (fullSupportSymbolicH S g).card = g.x*g.z-1 +
      min (pair12Count S.D-2) (pair13Count S.D-1) +
      (pair13Count S.D-1-g.x)+(pair13Count S.D-2-g.x) :=
  t3_unit_y_H_card S hg hf ho ht hy hx hz
-- These contracts detect a missing C=2 guard or a false r>s specialization.
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=4) (hs : pair13Count S.D=4)
    (hx : g.x=3) (hy : g.y=1) (hz : g.z=2) : (fullSupportSymbolicH S g).card=7 := by
  have h := t3_unit_y_H_card S hg hf ho ht hy (by omega) (by omega)
  norm_num [hr,hs,hx,hz] at h
  exact h
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=4) (hs : pair13Count S.D=4)
    (hx : g.x=2) (hy : g.y=1) (hz : g.z=3) : (fullSupportSymbolicH S g).card=8 := by
  have h := t3_unit_y_H_card S hg hf ho ht hy (by omega) (by omega)
  norm_num [hr,hs,hx,hz] at h
  exact h
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=4) (hs : pair13Count S.D=3)
    (hx : g.x=2) (hy : g.y=1) (hz : g.z=3) : (fullSupportSymbolicH S g).card=7 := by
  have h := t3_unit_y_H_card S hg hf ho ht hy (by omega) (by omega)
  norm_num [hr,hs,hx,hz] at h
  exact h
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3) (hs : pair13Count S.D=3)
    (hx : g.x=2) (hy : g.y=1) (hz : g.z=2) : (fullSupportSymbolicH S g).card=4 := by
  have h := t3_unit_y_H_card S hg hf ho ht hy (by omega) (by omega)
  norm_num [hr,hs,hx,hz] at h
  exact h
end NSP3
