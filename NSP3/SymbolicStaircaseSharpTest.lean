import NSP3.SymbolicCoordinateTransport

namespace NSP3
attribute [local instance] Classical.propDecidable
example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S) : noFullTarget S ≤ S.m :=
  noFull_symbolic_sharp S hnf
example (S : CyclicStaircase) :
    (if ∃ g, MinimalComplement S.D g ∧ FullSupport g then fullTarget S else noFullTarget S) ≤ S.m :=
  cyclicStaircase_symbolic_sharp S
end NSP3
