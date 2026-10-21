import NSP3.Residue

namespace NSP3

/-- Gcd of all four inputs is enough: none of a,b,c must itself be a unit. -/
theorem apery_residue_surjective (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    Function.Surjective (residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m)) := by
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  have h0 := Nat.gcd_eq_gcd_ab m (Nat.gcd a (Nat.gcd b c))
  rw [hgcd] at h0
  have h1 := Nat.gcd_eq_gcd_ab a (Nat.gcd b c)
  have h2 := Nat.gcd_eq_gcd_ab b c
  have z0 := congrArg (fun z : ℤ => (z : ZMod m)) h0
  have z1 := congrArg (fun z : ℤ => (z : ZMod m)) h1
  have z2 := congrArg (fun z : ℤ => (z : ZMod m)) h2
  push_cast at z0 z1 z2
  rw [ZMod.natCast_self, zero_mul, zero_add] at z0
  rw [z1, z2] at z0
  let A : ZMod m := (Nat.gcdA a (Nat.gcd b c) : ZMod m) *
    (Nat.gcdB m (Nat.gcd a (Nat.gcd b c)) : ZMod m)
  let B : ZMod m := (Nat.gcdA b c : ZMod m) *
    (Nat.gcdB a (Nat.gcd b c) : ZMod m) *
    (Nat.gcdB m (Nat.gcd a (Nat.gcd b c)) : ZMod m)
  let C : ZMod m := (Nat.gcdB b c : ZMod m) *
    (Nat.gcdB a (Nat.gcd b c) : ZMod m) *
    (Nat.gcdB m (Nat.gcd a (Nat.gcd b c)) : ZMod m)
  have hcomb : (a : ZMod m)*A + (b : ZMod m)*B + (c : ZMod m)*C = 1 := by
    dsimp [A, B, C]
    linear_combination -z0
  intro r
  refine ⟨⟨(r*A).val, (r*B).val, (r*C).val⟩, ?_⟩
  simp only [residueOf, ZMod.natCast_zmod_val]
  calc
    (r*A)*a + (r*B)*b + (r*C)*c = r*((a : ZMod m)*A + (b : ZMod m)*B + (c : ZMod m)*C) := by ring
    _ = r := by rw [hcomb, mul_one]

theorem residueOf_add {m : ℕ} (a b c : ZMod m) (p q : Point3) :
    residueOf a b c (p + q) = residueOf a b c p + residueOf a b c q := by
  simp only [residueOf, Point3.add_x, Point3.add_y, Point3.add_z, Nat.cast_add]
  ring

end NSP3
