import NSP3.SymbolicBWBulk

namespace NSP3

example (r s t : ℕ) (hr : s ≤ r) (hs : t ≤ s)
    (ht : t=4 ∨ t=5 ∨ t=6)
    (hne : ¬ ((t=4 ∧ s=4 ∧ r≤7) ∨ (t=4 ∧ s=5 ∧ r≤6) ∨
      (t=4 ∧ s=6 ∧ r=6) ∨ (t=5 ∧ s=5 ∧ r=5))) :
    (r+s+t+2)^2 ≤ 4*(1+3*r+Nat.choose r 2+Nat.choose s 2+Nat.choose t 2+
      (coreCardRows r s t-largeHoleCap t)+3) :=
  smallwidth_core_bulk_square r s t hr hs ht hne

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=4 ∨ pair23Count S.D=5 ∨ pair23Count S.D=6)
    (hne : ¬ ((pair23Count S.D=4 ∧ pair13Count S.D=4 ∧ pair12Count S.D≤7) ∨
      (pair23Count S.D=4 ∧ pair13Count S.D=5 ∧ pair12Count S.D≤6) ∨
      (pair23Count S.D=4 ∧ pair13Count S.D=6 ∧ pair12Count S.D=6) ∨
      (pair23Count S.D=5 ∧ pair13Count S.D=5 ∧ pair12Count S.D=5))) :
    fullTarget S ≤ fullSupportSymbolicBW S g :=
  fullSupport_smallwidth_core_bulk_BW_sharp S hg hf ho ht hne

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : 4 ≤ pair23Count S.D) :
    fullTarget S ≤ S.m ∨
      ((pair12Count S.D=6 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
       (pair12Count S.D=7 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
       (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
       (pair12Count S.D=6 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
       (pair12Count S.D=6 ∧ pair13Count S.D=6 ∧ pair23Count S.D=4) ∨
       (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=5)) :=
  fullSupport_tGE4_six_profile_cover S hg hf ho ht

end NSP3
