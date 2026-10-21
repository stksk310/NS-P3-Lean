import NSP3.PresentationGeometry

namespace NSP3

/-- Least reflexive, symmetric, transitive, additive-context closure of the supplied edges. -/
inductive PresentationRel (R : Finset (Fact4 × Fact4)) : Fact4 → Fact4 → Prop
  | edge {u v} : (u,v) ∈ R → PresentationRel R u v
  | refl (u) : PresentationRel R u u
  | symm {u v} : PresentationRel R u v → PresentationRel R v u
  | trans {u v w} : PresentationRel R u v → PresentationRel R v w → PresentationRel R u w
  | context {u v} : PresentationRel R u v → (d : Fact4) → PresentationRel R (u+d) (v+d)

theorem presentationRel_sound (m a b c : ℕ) (R : Finset (Fact4 × Fact4))
    (hs : ∀ e ∈ R, factorWeight m a b c e.1 = factorWeight m a b c e.2)
    {u v : Fact4} (h : PresentationRel R u v) :
    factorWeight m a b c u = factorWeight m a b c v := by
  induction h with
  | edge he => exact hs _ he
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | context _ d ih => simp only [factorWeight_add, ih]

/-- Universal property prevents an unproved generation assumption in the closure. -/
theorem presentationRel_least (R : Finset (Fact4 × Fact4)) (C : Fact4 → Fact4 → Prop)
    (he : ∀ e ∈ R, C e.1 e.2) (hr : ∀ u, C u u)
    (hs : ∀ u v, C u v → C v u)
    (ht : ∀ u v w, C u v → C v w → C u w)
    (ha : ∀ u v, C u v → ∀ d, C (u+d) (v+d))
    {u v : Fact4} (h : PresentationRel R u v) : C u v := by
  induction h with
  | edge h => exact he _ h
  | refl u => exact hr u
  | symm _ ih => exact hs _ _ ih
  | trans _ _ ih₁ ih₂ => exact ht _ _ _ ih₁ ih₂
  | context _ d ih => exact ha _ _ ih d

/-- A finite presentation of the actual numeric kernel. -/
def IsFactorPresentation (m a b c : ℕ) (R : Finset (Fact4 × Fact4)) : Prop :=
  ∀ u v, PresentationRel R u v ↔ factorWeight m a b c u = factorWeight m a b c v

theorem factorWeight_image (m a b c n : ℕ) :
    (∃ u : Fact4, factorWeight m a b c u = n) ↔ n ∈ generatedSemigroup m a b c := by
  rw [mem_generatedSemigroup_iff]
  constructor
  · rintro ⟨⟨k,p⟩, h⟩
    exact ⟨k,p,h.symm⟩
  · rintro ⟨k,p,h⟩
    exact ⟨(k,p),h.symm⟩

end NSP3
