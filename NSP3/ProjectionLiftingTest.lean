import NSP3.ProjectionLifting

namespace NSP3

example (p : Point3) : (proj12 p).x = p.x := rfl
example (p : Point3) : (proj12 p).y = p.y := rfl
example (p : Point3) : (proj12 p).z = 0 := rfl
example (p : Point3) : (proj13 p).x = p.x := rfl
example (p : Point3) : (proj13 p).y = 0 := rfl
example (p : Point3) : (proj13 p).z = p.z := rfl
example (p : Point3) : (proj23 p).x = 0 := rfl
example (p : Point3) : (proj23 p).y = p.y := rfl
example (p : Point3) : (proj23 p).z = p.z := rfl

example (p : Point3) : proj12 p ≤ p := proj12_le p
example (p : Point3) : proj13 p ≤ p := proj13_le p
example (p : Point3) : proj23 p ≤ p := proj23_le p

example (S : CyclicStaircase) (hnf : NoFullSupportBoundary S) (p : Point3)
    (hx : 0 < p.x) (hy : 0 < p.y) (hz : 0 < p.z)
    (h12 : proj12 p ∈ S.D) (h13 : proj13 p ∈ S.D) (h23 : proj23 p ∈ S.D) :
    p ∈ S.D :=
  noFull_projection_lifting S hnf p hx hy hz h12 h13 h23

end NSP3
