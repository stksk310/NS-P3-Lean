import NSP3.SymbolicT3TwoUnitArithmetic
namespace NSP3
example (r s w : ℤ) :
    2*r*(r-1)+2*s*(s-1)+20*r+12*s+4*w-20-(r+s+5)^2=
      (r-s)^2+8*r+4*w-45 := two_unit_square_gap_identity r s w
example (r s w m : ℕ) (hs : 3 ≤ s) (hr : s ≤ r) (h4 : 4 ≤ r)
    (hw : 2 ≤ w) (hw4 : 4 ≤ s→4 ≤ w)
    (hb : Nat.choose r 2+Nat.choose s 2+5*r+3*s+w ≤ m+5)
    (hb' : s<r→Nat.choose r 2+Nat.choose s 2+5*r+3*s+w ≤ m+4) :
    (r+s+5)^2 ≤ 4*m := two_unit_budget_square r s w m hs hr h4 hw hw4 hb hb'
example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hx : g.x=1) (hu : g.y=1 ∨ g.z=1) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      5*pair12Count S.D+3*pair13Count S.D+
      ferrersW (if g.y=1 then pair12Count S.D else pair13Count S.D) 1 1 ≤ 
        fullSupportSymbolicBW S g+5 := t3_two_unit_BW_coarse S hg hf ho ht hx hu
example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hx : g.x=1) (hu : g.y=1 ∨ g.z=1) (hn : pair13Count S.D<pair12Count S.D) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      5*pair12Count S.D+3*pair13Count S.D+
      ferrersW (if g.y=1 then pair12Count S.D else pair13Count S.D) 1 1 ≤ 
        fullSupportSymbolicBW S g+4 := t3_two_unit_BW_nonbalanced S hg hf ho ht hx hu hn
example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hx : g.x=1) (hu : g.y=1 ∨ g.z=1) :
    fullTarget S ≤ S.m ∨ (pair12Count S.D=3 ∧ pair13Count S.D=3 ∧
      ((g.y=3 ∧ g.z=1) ∨ (g.y=1 ∧ g.z=3))) :=
  fullSupport_t3_two_unit_BW_cover S hg hf ho ht hx hu
end NSP3
