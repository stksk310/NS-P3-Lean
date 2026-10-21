import NSP3.AperyCoverage

namespace NSP3

def aperyWeight (a b c : ℕ) (q : Point3) : ℕ := a*q.x + b*q.y + c*q.z

/-- Weight first, then a global lexicographic tie rule on x,y,z. -/
def aperyKey (a b c : ℕ) (q : Point3) : ℕ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)) :=
  toLex (aperyWeight a b c q, toLex (q.x, toLex (q.y, q.z)))

theorem aperyWeight_add (a b c : ℕ) (p q : Point3) :
    aperyWeight a b c (p+q) = aperyWeight a b c p + aperyWeight a b c q := by
  simp only [aperyWeight, Point3.add_x, Point3.add_y, Point3.add_z]
  ring

theorem aperyKey_injective (a b c : ℕ) : Function.Injective (aperyKey a b c) := by
  intro p q h
  change (aperyWeight a b c p, (p.x, (p.y, p.z))) =
    (aperyWeight a b c q, (q.x, (q.y, q.z))) at h
  apply Point3.ext
  · exact congrArg (fun t : ℕ × (ℕ × (ℕ × ℕ)) => t.2.1) h
  · exact congrArg (fun t : ℕ × (ℕ × (ℕ × ℕ)) => t.2.2.1) h
  · exact congrArg (fun t : ℕ × (ℕ × (ℕ × ℕ)) => t.2.2.2) h

/-- Exact additive compatibility, including all equal-weight ties. -/
theorem aperyKey_add (a b c : ℕ) (p q : Point3) :
    aperyKey a b c (p+q) = aperyKey a b c p + aperyKey a b c q := by
  change toLex (aperyWeight a b c (p+q), toLex (p.x+q.x, toLex (p.y+q.y,p.z+q.z))) =
    toLex (aperyWeight a b c p + aperyWeight a b c q,
      toLex (p.x+q.x, toLex (p.y+q.y,p.z+q.z)))
  rw [aperyWeight_add]

def AperyCanonical (m a b c : ℕ) (q : Point3) : Prop :=
  ∀ u : Point3,
    residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) u =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q →
    aperyKey a b c q ≤ aperyKey a b c u

theorem aperyCanonical_unique (m a b c : ℕ) {p q : Point3}
    (hp : AperyCanonical m a b c p) (hq : AperyCanonical m a b c q)
    (hr : residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q) : p = q :=
  aperyKey_injective a b c (le_antisymm (hp q hr.symm) (hq p hr))

/-- The exchange argument for every coordinatewise lower point at once. -/
theorem aperyCanonical_downward (m a b c : ℕ) {p q : Point3}
    (hpq : p ≤ q) (hq : AperyCanonical m a b c q) : AperyCanonical m a b c p := by
  have hx : p.x ≤ q.x := hpq.1
  have hy : p.y ≤ q.y := hpq.2.1
  have hz : p.z ≤ q.z := hpq.2.2
  let d : Point3 := ⟨q.x-p.x, q.y-p.y, q.z-p.z⟩
  have hpd : p+d=q := by
    apply Point3.ext <;> simp [d] <;> omega
  intro u hu
  have hr : residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) (u+d) =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q := by
    rw [residueOf_add, hu, ← residueOf_add, hpd]
  have hbound := hq (u+d) hr
  rw [← hpd, aperyKey_add, aperyKey_add] at hbound
  exact (add_le_add_iff_right _).mp hbound

theorem aperyCanonical_exists (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) (r : ZMod m) :
    ∃ q : Point3,
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q = r ∧
      AperyCanonical m a b c q := by
  have wf : WellFounded (fun p q : Point3 => aperyKey a b c p < aperyKey a b c q) :=
    InvImage.wf (aperyKey a b c) wellFounded_lt
  obtain ⟨q, hq, hmin⟩ := wf.has_min
    {q : Point3 | residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q = r}
    (apery_residue_surjective m a b c hm hgcd r)
  refine ⟨q, hq, ?_⟩
  intro u hu
  exact le_of_not_gt (hmin u (hu.trans hq))

theorem aperyCanonical_weight_min (m a b c : ℕ) {q u : Point3}
    (hq : AperyCanonical m a b c q)
    (hr : residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) u =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q) :
    aperyWeight a b c q ≤ aperyWeight a b c u :=
  Prod.Lex.monotone_fst (aperyKey a b c q) (aperyKey a b c u) (hq u hr)

end NSP3
