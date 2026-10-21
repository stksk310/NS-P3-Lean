import NSP3.FullResidualCompleteness

namespace NSP3

#check fullSupport_counterexample_mem_residual

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hcounter : S.m ≤ fullTarget S) :
    FullResidualTuple.mk
      (pair12Count S.D) (pair13Count S.D) (pair23Count S.D) ∈
        fullResidualTupleFinset :=
  fullSupport_counterexample_mem_residual S hg hfull hord hcounter

end NSP3
