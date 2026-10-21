import NSP3.Basic

namespace NSP3

example : (Point3.zero).x = 0 := by simp
example : (Point3.e1).x = 1 := by simp
example : (Point3.e2).y = 1 := by simp
example : (Point3.e3).z = 1 := by simp

example (p : Point3) (h : 0 < p.x) : (p.pred1).x + 1 = p.x := by
  simp [Point3.pred1, Nat.sub_add_cancel h]

example (p : Point3) (h : 0 < p.y) : (p.pred2).y + 1 = p.y := by
  simp [Point3.pred2, Nat.sub_add_cancel h]

example (p : Point3) (h : 0 < p.z) : (p.pred3).z + 1 = p.z := by
  simp [Point3.pred3, Nat.sub_add_cancel h]

end NSP3
