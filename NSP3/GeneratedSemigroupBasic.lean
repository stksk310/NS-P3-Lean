import NSP3.AperyBridge

namespace NSP3

/-- Actual nonnegative integer combinations of the four numeric inputs. -/
def generatedSemigroup (m a b c : ℕ) : Set ℕ :=
  {n | ∃ k x y z : ℕ, n = k*m + a*x + b*y + c*z}

def generatedApery (m a b c : ℕ) : Set ℕ :=
  {n | n ∈ generatedSemigroup m a b c ∧
    (n < m ∨ n-m ∉ generatedSemigroup m a b c)}

theorem mem_generatedSemigroup_iff (m a b c n : ℕ) :
    n ∈ generatedSemigroup m a b c ↔
      ∃ k : ℕ, ∃ p : Point3, n = k*m + aperyWeight a b c p := by
  constructor
  · rintro ⟨k,x,y,z,rfl⟩
    refine ⟨k,⟨x,y,z⟩,?_⟩
    simp only [aperyWeight]
    ring
  · rintro ⟨k,p,h⟩
    refine ⟨k,p.x,p.y,p.z,?_⟩
    rw [h]
    simp only [aperyWeight]
    ring

theorem generatedSemigroup_zero (m a b c : ℕ) : 0 ∈ generatedSemigroup m a b c := by
  exact ⟨0,0,0,0,by simp⟩

theorem generatedSemigroup_mul_mem (m a b c k : ℕ) : k*m ∈ generatedSemigroup m a b c := by
  exact ⟨k,0,0,0,by simp⟩

theorem aperyWeight_mem_generatedSemigroup (m a b c : ℕ) (p : Point3) :
    aperyWeight a b c p ∈ generatedSemigroup m a b c :=
  (mem_generatedSemigroup_iff m a b c _).mpr ⟨0,p,by simp⟩

theorem generatedSemigroup_generators (m a b c : ℕ) :
    m ∈ generatedSemigroup m a b c ∧ a ∈ generatedSemigroup m a b c ∧
      b ∈ generatedSemigroup m a b c ∧ c ∈ generatedSemigroup m a b c := by
  exact ⟨⟨1,0,0,0,by simp⟩,⟨0,1,0,0,by simp⟩,
    ⟨0,0,1,0,by simp⟩,⟨0,0,0,1,by simp⟩⟩

theorem generatedSemigroup_add (m a b c : ℕ) {n l : ℕ}
    (hn : n ∈ generatedSemigroup m a b c) (hl : l ∈ generatedSemigroup m a b c) :
    n+l ∈ generatedSemigroup m a b c := by
  obtain ⟨k,p,hp⟩ := (mem_generatedSemigroup_iff m a b c n).mp hn
  obtain ⟨j,q,hq⟩ := (mem_generatedSemigroup_iff m a b c l).mp hl
  apply (mem_generatedSemigroup_iff m a b c _).mpr
  refine ⟨k+j,p+q,?_⟩
  rw [aperyWeight_add,hp,hq]
  ring

def generatedAddSubmonoid (m a b c : ℕ) : AddSubmonoid ℕ where
  carrier := generatedSemigroup m a b c
  zero_mem' := generatedSemigroup_zero m a b c
  add_mem' := generatedSemigroup_add m a b c

theorem aperyWeight_cast (m a b c : ℕ) (p : Point3) :
    (aperyWeight a b c p : ZMod m) = residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p := by
  simp only [aperyWeight,residueOf,Nat.cast_add,Nat.cast_mul]
  ring

/-- Order is explicit before extracting a nonnegative multiple from congruence. -/
theorem nat_eq_add_mul_of_cast_eq (m n w : ℕ) (hw : w ≤ n)
    (h : (n : ZMod m) = (w : ZMod m)) : ∃ k : ℕ, n = w+k*m := by
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hw
  have hz : (d : ZMod m) = 0 := by
    rw [hd,Nat.cast_add] at h
    exact add_left_cancel (h.trans (add_zero _).symm)
  obtain ⟨k,hk⟩ := (ZMod.natCast_eq_zero_iff d m).mp hz
  refine ⟨k,?_⟩
  rw [hd,hk]
  ring

end NSP3
