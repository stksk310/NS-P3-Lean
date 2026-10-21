import NSP3.Downset

namespace NSP3

/-- An immediate-predecessor presentation of a minimal point outside a down-set. -/
def MinimalComplement (D : Finset Point3) (b : Point3) : Prop :=
  b ∉ D ∧
    (0 < b.x → b.pred1 ∈ D) ∧
    (0 < b.y → b.pred2 ∈ D) ∧
    (0 < b.z → b.pred3 ∈ D)

namespace MinimalComplement

theorem not_mem {D : Finset Point3} {b : Point3} (hb : MinimalComplement D b) : b ∉ D :=
  hb.1

theorem pred1_mem {D : Finset Point3} {b : Point3} (hb : MinimalComplement D b)
    (h : 0 < b.x) : b.pred1 ∈ D :=
  hb.2.1 h

theorem pred2_mem {D : Finset Point3} {b : Point3} (hb : MinimalComplement D b)
    (h : 0 < b.y) : b.pred2 ∈ D :=
  hb.2.2.1 h

theorem pred3_mem {D : Finset Point3} {b : Point3} (hb : MinimalComplement D b)
    (h : 0 < b.z) : b.pred3 ∈ D :=
  hb.2.2.2 h

end MinimalComplement

def Pure1 (b : Point3) : Prop := 0 < b.x ∧ b.y = 0 ∧ b.z = 0
def Pure2 (b : Point3) : Prop := b.x = 0 ∧ 0 < b.y ∧ b.z = 0
def Pure3 (b : Point3) : Prop := b.x = 0 ∧ b.y = 0 ∧ 0 < b.z

def Pair12 (b : Point3) : Prop := 0 < b.x ∧ 0 < b.y ∧ b.z = 0
def Pair13 (b : Point3) : Prop := 0 < b.x ∧ b.y = 0 ∧ 0 < b.z
def Pair23 (b : Point3) : Prop := b.x = 0 ∧ 0 < b.y ∧ 0 < b.z

def FullSupport (b : Point3) : Prop := 0 < b.x ∧ 0 < b.y ∧ 0 < b.z

/-- Two points have intersecting positive support. -/
def SupportInter (b c : Point3) : Prop :=
  (0 < b.x ∧ 0 < c.x) ∨ (0 < b.y ∧ 0 < c.y) ∨ (0 < b.z ∧ 0 < c.z)

end NSP3
