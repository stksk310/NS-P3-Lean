import NSP3.FullTarget

namespace NSP3

theorem fullSupportBoundary_unique (S : CyclicStaircase) {g h : Point3}
    (hg : MinimalComplement S.D g) (hfullg : FullSupport g)
    (hh : MinimalComplement S.D h) (hfullh : FullSupport h) : g = h :=
  fullSupport_minimalComplement_atMostOne S hg hh hfullg hfullh

theorem fullSupportBoundary_return_zero (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    S.rho g = Point3.zero := fullSupport_return_eq_zero S hg hfull

theorem pair12Boundary_return_ne_zero (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (b : Pair12Boundary S) : S.rho b.1 ≠ Point3.zero :=
  pair12_return_ne_zero_of_fullSupport S hg hfull b.2.1 b.2.2

theorem pair13Boundary_return_ne_zero (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (b : Pair13Boundary S) : S.rho b.1 ≠ Point3.zero :=
  pair13_return_ne_zero_of_fullSupport S hg hfull b.2.1 b.2.2

theorem pair23Boundary_return_ne_zero (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (b : Pair23Boundary S) : S.rho b.1 ≠ Point3.zero :=
  pair23_return_ne_zero_of_fullSupport S hg hfull b.2.1 b.2.2

end NSP3
