import NSP3.MinimalGeneratorClass

namespace NSP3

abbrev SemigroupAtomType (S : Set ℕ) := {n : ℕ // SemigroupAtom S n}
abbrev AtomCoefficients (S : Set ℕ) := SemigroupAtomType S →₀ ℕ

/-- The numeric map on the free commutative monoid on actual atoms, for any carrier. -/
def atomWeight (S : Set ℕ) (v : AtomCoefficients S) : ℕ :=
  v.sum (fun t k => k*t.val)

theorem atomWeight_add (S : Set ℕ) (u v : AtomCoefficients S) :
    atomWeight S (u+v) = atomWeight S u + atomWeight S v := by
  classical
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => Nat.add_mul _ _ _)

def inputAtom (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) (i : Fin 4) :
    SemigroupAtomType (generatedSemigroup m a b c) :=
  ⟨![m,a,b,c] i, h.atoms _ (by fin_cases i <;> simp)⟩

noncomputable def inputAtomEquiv (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    Fin 4 ≃ SemigroupAtomType (generatedSemigroup m a b c) :=
  Equiv.ofBijective (inputAtom m a b c h) (by
    constructor
    · intro i j he
      have he' := congrArg Subtype.val he
      have hd := h.distinct
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
      fin_cases i <;> fin_cases j <;> simp_all [inputAtom]
    · intro t
      have ht := (minimalFour_atom_iff m a b c t.val h).mp t.property
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with ht | ht | ht | ht
      · exact ⟨0, Subtype.ext (by simpa [inputAtom] using ht.symm)⟩
      · exact ⟨1, Subtype.ext (by simpa [inputAtom] using ht.symm)⟩
      · exact ⟨2, Subtype.ext (by simpa [inputAtom] using ht.symm)⟩
      · exact ⟨3, Subtype.ext (by simpa [inputAtom] using ht.symm)⟩)

def fourCoordinates : Fact4 ≃+ (Fin 4 → ℕ) where
  toFun u := ![u.1,u.2.x,u.2.y,u.2.z]
  invFun v := (v 0, ⟨v 1,v 2,v 3⟩)
  left_inv u := by cases u with | mk k p => cases p; rfl
  right_inv v := by funext i; fin_cases i <;> rfl
  map_add' u v := by funext i; fin_cases i <;> rfl

/-- Coordinates are indexed by actual atom values, not by an assumed abstract four-set. -/
noncomputable def atomFactorEquiv (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    Fact4 ≃+ AtomCoefficients (generatedSemigroup m a b c) := by
  let e := inputAtomEquiv m a b c h
  let : Fintype (SemigroupAtomType (generatedSemigroup m a b c)) := Fintype.ofEquiv (Fin 4) e
  exact {
    toFun := fun u => Finsupp.equivFunOnFinite.symm (fun t => fourCoordinates u (e.symm t))
    invFun := fun v => fourCoordinates.symm (fun i => v (e i))
    left_inv := by intro u; simp
    right_inv := by intro v; ext t; simp
    map_add' := by intro u v; ext t; exact congrFun (fourCoordinates.map_add u v) (e.symm t) }

theorem atomFactorEquiv_apply (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (u : Fact4) (t : SemigroupAtomType (generatedSemigroup m a b c)) :
    atomFactorEquiv m a b c h u t = fourCoordinates u ((inputAtomEquiv m a b c h).symm t) := rfl

theorem atomFactorEquiv_weight (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (u : Fact4) : atomWeight _ (atomFactorEquiv m a b c h u) = factorWeight m a b c u := by
  classical
  let e := inputAtomEquiv m a b c h
  let : Fintype (SemigroupAtomType (generatedSemigroup m a b c)) := Fintype.ofEquiv (Fin 4) e
  unfold atomWeight
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  rw [← e.sum_comp]
  simp only [atomFactorEquiv_apply, e, Equiv.symm_apply_apply]
  simp only [Fin.sum_univ_succ]
  change u.1*m + (u.2.x*a + (u.2.y*b + (u.2.z*c + 0))) = factorWeight m a b c u
  unfold factorWeight aperyWeight
  ring

theorem atomWeight_image (m a b c n : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    (∃ v : AtomCoefficients (generatedSemigroup m a b c), atomWeight _ v = n) ↔
      n ∈ generatedSemigroup m a b c := by
  rw [← factorWeight_image]
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨(atomFactorEquiv m a b c h).symm v, ?_⟩
    rw [← atomFactorEquiv_weight m a b c h, AddEquiv.apply_symm_apply]
    exact hv
  · rintro ⟨u,hu⟩
    exact ⟨atomFactorEquiv m a b c h u, (atomFactorEquiv_weight m a b c h u).trans hu⟩

end NSP3
