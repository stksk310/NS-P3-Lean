import NSP3.SymbolicSmallwidthQ544

namespace NSP3

example (A B C : ℕ) (ha : 1 ≤ A) (hb : 1 ≤ B) (hc : 1 ≤ C)
    (ha4 : A ≤ 4) (hb4 : B ≤ 4) (hc3 : C ≤ 3) :
    7 ≤ max (ferrersPlaneDefect 5 A B) (rankCutPhi 5 A B)+
      max (ferrersPlaneDefect 4 A C) (rankCutPhi 4 A C)+
      max (ferrersPlaneDefect 4 B C) (rankCutPhi 4 B C) :=
  ferrers_weighted_544_small_triangle_lower A B C ha hb hc ha4 hb4 hc3

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hr : pair12Count S.D=5) (hs : pair13Count S.D=4) (ht : pair23Count S.D=4) :
    57 ≤ fullSupportSymbolicBF S g := fullSupport_q544_BF_sharp_lower S hg hf ho hr hs ht

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hr : pair12Count S.D=5) (hs : pair13Count S.D=4) (ht : pair23Count S.D=4) :
    fullTarget S ≤ S.m := fullSupport_t4_q544_symbolic_sharp S hg hf ho hr hs ht

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : 4 ≤ pair23Count S.D) :
    fullTarget S ≤ S.m ∨ (pair12Count S.D ≤ 17 ∧
      pair12Count S.D+6 < 2*(pair13Count S.D+pair23Count S.D) ∧
      ((pair23Count S.D=4 ∧ pair13Count S.D ≤ 8) ∨
       (pair23Count S.D=5 ∧ pair13Count S.D ≤ 6) ∨
       (pair23Count S.D=6 ∧ pair13Count S.D=6)) ∧
      ¬ (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∧
      ¬ (pair12Count S.D=5 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4)) :=
  fullSupport_smallwidth_refined_cover S hg hf ho ht

end NSP3
