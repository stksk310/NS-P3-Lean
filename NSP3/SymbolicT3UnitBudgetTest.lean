import NSP3.SymbolicT3UnitBudget

namespace NSP3

example (r A : ℕ) (ha : 0 < A) (hr : A+1 ≤ r) : A ≤ ferrersW r A 1 :=
  ferrers_unit_W_first r A ha hr

example (r A : ℕ) (ha : 0 < A) (hr : A+2 ≤ r) : 2*A ≤ ferrersW r A 1 :=
  ferrers_unit_W_two r A ha hr

example (r A B : ℕ) (ha : 2 ≤ A) (hb : 2 ≤ B) (hcap : r+2 ≤ A+B) :
    3 ≤ (ferrersRectangle r A B).card :=
  ferrers_rectangle_three_corners r A B ha hb hcap

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hz : g.z = 1) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) :
    1 + 3*pair12Count S.D + Nat.choose (pair12Count S.D) 2 +
      Nat.choose (pair13Count S.D) 2 + g.x*g.y + pair13Count S.D +
      (pair13Count S.D-1-g.x) +
      (min (pair12Count S.D-2) (pair13Count S.D-1)-g.x) +
      (ferrersRectangle (pair12Count S.D) g.x g.y).card +
      ferrersPlaneDefect (pair13Count S.D) g.x 1 + ferrersPlaneDefect 3 g.y 1 ≤ S.m :=
  fullSupport_t3_unit_z_resource_lower S hg hf ho ht hz hx hy

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hz : g.z = 1) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y)
    (hcap : pair12Count S.D+2 ≤ g.x+g.y) : fullTarget S ≤ S.m :=
  fullSupport_t3_unit_z_slack_sharp S hg hf ho ht hz hx hy hcap

end NSP3
