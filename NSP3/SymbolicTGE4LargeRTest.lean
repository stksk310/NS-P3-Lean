import NSP3.SymbolicTGE4LargeR

namespace NSP3

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) :
    pair12Count S.D-1 ≤ (fullSupportSymbolicH S g).card :=
  fullSupport_symbolic_H_capacity_lower S hg hf ho

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (hr : 1 ≤ pair12Count S.D) :
    4*pair12Count S.D+3+Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+Nat.choose (pair23Count S.D) 2 ≤
        fullSupportSymbolicBW S g :=
  fullSupport_symbolic_BW_capacity_lower S hg hf ho hr

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (hr : 18 ≤ pair12Count S.D)
    (hw : pair13Count S.D+pair23Count S.D ≤ 12) : fullTarget S ≤ S.m :=
  fullSupport_tGE4_smallwidth_large_r_sharp S hg hf ho hr hw

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hsum : 8 ≤ pair13Count S.D+pair23Count S.D)
    (hr : 2*(pair13Count S.D+pair23Count S.D) ≤ pair12Count S.D+6) :
    fullTarget S ≤ S.m := fullSupport_variable_threshold_symbolic_sharp S hg hf ho hsum hr

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : 4 ≤ pair23Count S.D)
    (hr : 18 ≤ pair12Count S.D) : fullTarget S ≤ S.m :=
  fullSupport_tGE4_large_r_symbolic_sharp S hg hf ho ht hr

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : 4 ≤ pair23Count S.D) :
    fullTarget S ≤ S.m ∨ (pair12Count S.D ≤ 17 ∧
      pair12Count S.D+6 < 2*(pair13Count S.D+pair23Count S.D) ∧
      ((pair23Count S.D=4 ∧ pair13Count S.D ≤ 8) ∨
       (pair23Count S.D=5 ∧ pair13Count S.D ≤ 6) ∨
       (pair23Count S.D=6 ∧ pair13Count S.D=6))) :=
  fullSupport_tGE4_reduced_cover S hg hf ho ht

end NSP3
