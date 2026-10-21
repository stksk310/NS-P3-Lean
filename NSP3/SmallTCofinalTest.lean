import NSP3.SmallTCofinal

namespace NSP3

#check fullSupport_t3_cofinal_strict
#check fullSupport_t2_cofinal_strict
#check fullSupport_t1_cofinal_strict
#check fullSupport_t0_strict
#check fullSupport_t3_gap_le_five_of_counterexample

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 3)
    (hr : 16 ≤ pair12Count S.D) : fullTarget S < S.m :=
  fullSupport_t3_cofinal_strict S hg hfull hord ht hr

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 3)
    (hr : pair12Count S.D = 16) : fullTarget S < S.m := by
  apply fullSupport_t3_cofinal_strict S hg hfull hord ht
  omega

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 2)
    (hr : pair12Count S.D = 10) : fullTarget S < S.m := by
  apply fullSupport_t2_cofinal_strict S hg hfull hord ht
  omega

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 1)
    (hr : pair12Count S.D = 4) : fullTarget S < S.m := by
  apply fullSupport_t1_cofinal_strict S hg hfull hord ht
  omega

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 3)
    (hcounter : S.m ≤ fullTarget S) :
    pair12Count S.D ≤ pair13Count S.D + 5 :=
  fullSupport_t3_gap_le_five_of_counterexample S hg hfull hord ht hcounter

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D = 0) :
    fullTarget S < S.m := fullSupport_t0_strict S hg hfull hord ht

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S)
    (hr : pair12Count S.D = 0) (hs : pair13Count S.D = 0)
    (ht : pair23Count S.D = 0) : fullTarget S < S.m := by
  exact fullSupport_t0_strict S hg hfull hord ht

end NSP3
