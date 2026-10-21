import NSP3.SymbolicBWCompletion

namespace NSP3

example (r s t K L A B C : ℕ) (ht : 1 ≤ t) (hs : t ≤ s) (hr : s ≤ r)
    (ha : 1 ≤ A) (hb : 1 ≤ B) (hc : 1 ≤ C) (hk : K+r+s ≤ L+17)
    (hlarge : 7 ≤ A ∨ 7 ≤ B ∨ 7 ≤ C) :
    K ≤ max (A*B*C-1) L+ferrersPlaneDefect r A B+
      ferrersPlaneDefect s A C+ferrersPlaneDefect t B C :=
  bw_large_coordinate_pressure r s t K L A B C ht hs hr ha hb hc hk hlarge

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hq : (pair12Count S.D=6 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=7 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=6 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=6 ∧ pair13Count S.D=6 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=5)) :
    fullTarget S ≤ fullSupportSymbolicBW S g :=
  fullSupport_smallwidth_six_BW_lower S hg hf ho hq

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : 4 ≤ pair23Count S.D) (hr : pair12Count S.D ≤ 17)
    (hvar : pair12Count S.D+6 < 2*(pair13Count S.D+pair23Count S.D))
    (hstrip : (pair23Count S.D=4 ∧ pair13Count S.D≤8) ∨
      (pair23Count S.D=5 ∧ pair13Count S.D≤6) ∨
      (pair23Count S.D=6 ∧ pair13Count S.D=6))
    (hne444 : ¬ (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4)) :
    fullTarget S ≤ fullSupportSymbolicBF S g :=
  fullSupport_smallwidth_remaining_BF_lower S hg hf ho ht hr hvar hstrip hne444

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : 4 ≤ pair23Count S.D) : fullTarget S ≤ S.m :=
  fullSupport_tGE4_ordered_symbolic_sharp S hg hf ho ht

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    fullTarget S ≤ S.m :=
  fullSupport_ordered_symbolic_sharp S hg hf ho

end NSP3
