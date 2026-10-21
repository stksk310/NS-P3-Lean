import Mathlib

namespace NSP3

/-- A lattice point in `ℕ³`, with named coordinates for readable geometric proofs. -/
@[ext]
structure Point3 where
  x : ℕ
  y : ℕ
  z : ℕ
  deriving DecidableEq, Repr

namespace Point3

instance : Zero Point3 := ⟨⟨0, 0, 0⟩⟩

instance : Add Point3 := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩⟩

instance : LE Point3 :=
  ⟨fun a b => a.x ≤ b.x ∧ a.y ≤ b.y ∧ a.z ≤ b.z⟩

instance : PartialOrder Point3 where
  le_refl a := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  le_trans _ _ _ hab hbc :=
    ⟨Nat.le_trans hab.1 hbc.1, Nat.le_trans hab.2.1 hbc.2.1,
      Nat.le_trans hab.2.2 hbc.2.2⟩
  le_antisymm a b hab hba := by
    apply Point3.ext
    · exact Nat.le_antisymm hab.1 hba.1
    · exact Nat.le_antisymm hab.2.1 hba.2.1
    · exact Nat.le_antisymm hab.2.2 hba.2.2

def zero : Point3 := ⟨0, 0, 0⟩

def e1 : Point3 := ⟨1, 0, 0⟩
def e2 : Point3 := ⟨0, 1, 0⟩
def e3 : Point3 := ⟨0, 0, 1⟩

def pred1 (p : Point3) : Point3 := ⟨p.x - 1, p.y, p.z⟩
def pred2 (p : Point3) : Point3 := ⟨p.x, p.y - 1, p.z⟩
def pred3 (p : Point3) : Point3 := ⟨p.x, p.y, p.z - 1⟩

/-- Coordinate lookup indexed by `0,1,2`. -/
def coord (p : Point3) (i : Fin 3) : ℕ := ![p.x, p.y, p.z] i

@[simp] theorem zero_x : zero.x = 0 := rfl
@[simp] theorem zero_y : zero.y = 0 := rfl
@[simp] theorem zero_z : zero.z = 0 := rfl

@[simp] theorem e1_x : e1.x = 1 := rfl
@[simp] theorem e1_y : e1.y = 0 := rfl
@[simp] theorem e1_z : e1.z = 0 := rfl
@[simp] theorem e2_x : e2.x = 0 := rfl
@[simp] theorem e2_y : e2.y = 1 := rfl
@[simp] theorem e2_z : e2.z = 0 := rfl
@[simp] theorem e3_x : e3.x = 0 := rfl
@[simp] theorem e3_y : e3.y = 0 := rfl
@[simp] theorem e3_z : e3.z = 1 := rfl

@[simp] theorem add_x (a b : Point3) : (a + b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : Point3) : (a + b).y = a.y + b.y := rfl
@[simp] theorem add_z (a b : Point3) : (a + b).z = a.z + b.z := rfl

@[simp] theorem pred1_x (p : Point3) : p.pred1.x = p.x - 1 := rfl
@[simp] theorem pred1_y (p : Point3) : p.pred1.y = p.y := rfl
@[simp] theorem pred1_z (p : Point3) : p.pred1.z = p.z := rfl
@[simp] theorem pred2_x (p : Point3) : p.pred2.x = p.x := rfl
@[simp] theorem pred2_y (p : Point3) : p.pred2.y = p.y - 1 := rfl
@[simp] theorem pred2_z (p : Point3) : p.pred2.z = p.z := rfl
@[simp] theorem pred3_x (p : Point3) : p.pred3.x = p.x := rfl
@[simp] theorem pred3_y (p : Point3) : p.pred3.y = p.y := rfl
@[simp] theorem pred3_z (p : Point3) : p.pred3.z = p.z - 1 := rfl

theorem pred1_add_e1 (p : Point3) (h : 0 < p.x) : p.pred1 + e1 = p := by
  ext <;> simp [pred1, Nat.sub_add_cancel h]

theorem pred2_add_e2 (p : Point3) (h : 0 < p.y) : p.pred2 + e2 = p := by
  ext <;> simp [pred2, Nat.sub_add_cancel h]

theorem pred3_add_e3 (p : Point3) (h : 0 < p.z) : p.pred3 + e3 = p := by
  ext <;> simp [pred3, Nat.sub_add_cancel h]

theorem pred1_le (p : Point3) : p.pred1 ≤ p :=
  ⟨Nat.sub_le _ _, Nat.le_refl _, Nat.le_refl _⟩

theorem pred2_le (p : Point3) : p.pred2 ≤ p :=
  ⟨Nat.le_refl _, Nat.sub_le _ _, Nat.le_refl _⟩

theorem pred3_le (p : Point3) : p.pred3 ≤ p :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.sub_le _ _⟩

end Point3

end NSP3
