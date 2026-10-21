import NSP3.SymbolicT3UnitXBudget

namespace NSP3

-- Break caught: an algebraic identity valid only after unrecorded subtraction guards.
example (r s : ℤ) : 2*r*(r-1)+2*s*(s-1)+28*r+12*s-40-(r+s+5)^2=
    (r-s)^2+16*r-65 := t3_unit_x_square_gap_identity r s

-- Break caught: invented H/BW hypothesis, finite r bound, or lost resource constant.
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      3*pair12Count S.D+2*(g.y*g.z)+3*pair13Count S.D ≤ S.m+6 :=
  fullSupport_t3_unit_x_resource_lower S hg hf ho ht hx hy hz

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      7*pair12Count S.D+3*pair13Count S.D ≤ S.m+10 :=
  fullSupport_t3_unit_x_coarse_lower S hg hf ho ht hx hy hz

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z)
    (hr : 5 ≤ pair12Count S.D ∨
      (pair12Count S.D=4 ∧ pair13Count S.D=3)) : fullTarget S ≤ S.m :=
  fullSupport_t3_unit_x_large_sharp S hg hf ho ht hx hy hz hr

-- Break caught: finite diagnostic survivor pattern being assumed instead of proved.
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    fullTarget S ≤ S.m ∨
      (pair12Count S.D=3 ∧ pair13Count S.D=3 ∧ g.y=2 ∧ g.z=2) :=
  fullSupport_t3_unit_x_BW_cover S hg hf ho ht hx hy hz

end NSP3
