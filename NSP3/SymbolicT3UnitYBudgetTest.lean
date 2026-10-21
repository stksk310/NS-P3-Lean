import NSP3.SymbolicT3UnitYBudget
namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hy : g.y=1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z) :
    3*pair12Count S.D+Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      g.x*g.z+min (pair12Count S.D-2) (pair13Count S.D-1)+3+
      (pair13Count S.D-1-g.x)+(pair13Count S.D-2-g.x)+
      ferrersPlaneDefect (pair12Count S.D) g.x 1+
      (ferrersRectangle (pair13Count S.D) g.x g.z).card+
      ferrersPlaneDefect 3 1 g.z ≤ S.m :=
  fullSupport_t3_unit_y_resource_lower S hg hf ho ht hy hx hz
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hy : g.y=1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z)
    (hcap : pair12Count S.D+2 ≤ g.x+g.z) : fullTarget S ≤ S.m :=
  fullSupport_t3_unit_y_slack_sharp S hg hf ho ht hy hx hz hcap
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hy : g.y=1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z)
    (hrs : pair13Count S.D < pair12Count S.D) : fullTarget S ≤ S.m :=
  fullSupport_t3_unit_y_nonbalanced_sharp S hg hf ho ht hy hx hz hrs
end NSP3
