import NSP3.Boundary

namespace NSP3

example {D : Finset Point3} {b : Point3} (hb : MinimalComplement D b) : b ∉ D :=
  hb.not_mem

example {D : Finset Point3} {b : Point3} (hb : MinimalComplement D b) (h : 0 < b.x) :
    b.pred1 ∈ D := hb.pred1_mem h

example {D : Finset Point3} {b : Point3} (hb : MinimalComplement D b) (h : 0 < b.y) :
    b.pred2 ∈ D := hb.pred2_mem h

example {D : Finset Point3} {b : Point3} (hb : MinimalComplement D b) (h : 0 < b.z) :
    b.pred3 ∈ D := hb.pred3_mem h

example (b : Point3) : Pair12 b ↔ 0 < b.x ∧ 0 < b.y ∧ b.z = 0 := Iff.rfl
example (b : Point3) : Pair13 b ↔ 0 < b.x ∧ b.y = 0 ∧ 0 < b.z := Iff.rfl
example (b : Point3) : Pair23 b ↔ b.x = 0 ∧ 0 < b.y ∧ 0 < b.z := Iff.rfl
example (b : Point3) : FullSupport b ↔ 0 < b.x ∧ 0 < b.y ∧ 0 < b.z := Iff.rfl

example : Point3.zero.x = 0 := by simp

end NSP3
