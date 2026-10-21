import NSP3.AperyOrder

namespace NSP3

/-- Choice of a unique global weighted-lex minimum, not an arbitrary fiber point. -/
noncomputable def aperyRepresentative (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) (r : ZMod m) : Point3 :=
  Classical.choose (aperyCanonical_exists m a b c hm hgcd r)

theorem aperyRepresentative_spec (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) (r : ZMod m) :
    residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m)
      (aperyRepresentative m a b c hm hgcd r) = r ∧
      AperyCanonical m a b c (aperyRepresentative m a b c hm hgcd r) :=
  Classical.choose_spec (aperyCanonical_exists m a b c hm hgcd r)

noncomputable def aperyStandardSet (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) : Finset Point3 := by
  classical
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  exact Finset.univ.image (aperyRepresentative m a b c hm hgcd)

theorem mem_aperyStandardSet (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) (q : Point3) :
    q ∈ aperyStandardSet m a b c hm hgcd ↔ AperyCanonical m a b c q := by
  classical
  let _ : NeZero m := ⟨Nat.ne_of_gt hm⟩
  constructor
  · intro hq
    change q ∈ Finset.univ.image (aperyRepresentative m a b c hm hgcd) at hq
    obtain ⟨r, _, heq⟩ := Finset.mem_image.mp hq
    rw [← heq]
    exact (aperyRepresentative_spec m a b c hm hgcd r).2
  · intro hq
    let r := residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q
    have hs := aperyRepresentative_spec m a b c hm hgcd r
    have heq : aperyRepresentative m a b c hm hgcd r = q :=
      aperyCanonical_unique m a b c hs.2 hq hs.1
    change q ∈ Finset.univ.image (aperyRepresentative m a b c hm hgcd)
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, heq⟩

theorem aperyStandardSet_downset (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    IsDownset (aperyStandardSet m a b c hm hgcd) := by
  intro p q hpq hq
  exact (mem_aperyStandardSet m a b c hm hgcd p).mpr
    (aperyCanonical_downward m a b c hpq ((mem_aperyStandardSet m a b c hm hgcd q).mp hq))

noncomputable def aperyResidueEquiv (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    {q : Point3 // q ∈ aperyStandardSet m a b c hm hgcd} ≃ ZMod m :=
  Equiv.ofBijective (fun q => residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q.1) (by
    constructor
    · intro p q hr
      apply Subtype.ext
      exact aperyCanonical_unique m a b c
        ((mem_aperyStandardSet m a b c hm hgcd p.1).mp p.2)
        ((mem_aperyStandardSet m a b c hm hgcd q.1).mp q.2) hr
    · intro r
      have hs := aperyRepresentative_spec m a b c hm hgcd r
      exact ⟨⟨aperyRepresentative m a b c hm hgcd r,
        (mem_aperyStandardSet m a b c hm hgcd _).mpr hs.2⟩, hs.1⟩)

theorem aperyResidueEquiv_spec (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (q : {q : Point3 // q ∈ aperyStandardSet m a b c hm hgcd}) :
    aperyResidueEquiv m a b c hm hgcd q =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q.1 := rfl

/-- The exact requested existence theorem. No coverage/downset/minimum assumption is added. -/
theorem apery_staircase_exists (m a b c : ℕ) (hm : 0 < m)
    (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    ∃ D : Finset Point3, IsDownset D ∧
      ∃ e : {q : Point3 // q ∈ D} ≃ ZMod m,
        (∀ q, e q = residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q.1) ∧
        ∀ q ∈ D, ∀ u : Point3,
          residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) u =
            residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q →
          a*q.x + b*q.y + c*q.z ≤ a*u.x + b*u.y + c*u.z := by
  refine ⟨aperyStandardSet m a b c hm hgcd, aperyStandardSet_downset m a b c hm hgcd,
    aperyResidueEquiv m a b c hm hgcd, aperyResidueEquiv_spec m a b c hm hgcd, ?_⟩
  intro q hq u hu
  exact aperyCanonical_weight_min m a b c
    ((mem_aperyStandardSet m a b c hm hgcd q).mp hq) hu

end NSP3
