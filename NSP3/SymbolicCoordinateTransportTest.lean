import NSP3.SymbolicCoordinateTransport

namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) : fullTarget S ≤ S.m :=
  fullSupport_symbolic_sharp S hg hf
end NSP3
