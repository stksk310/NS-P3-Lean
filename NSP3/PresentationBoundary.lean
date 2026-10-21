import NSP3.PresentationRelations

namespace NSP3

theorem presentation_border_replacement (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (p : Point3) (hp : MinimalComplement (aperyStandardSet m a b c hm hgcd) p) :
    ∃ h : ℕ, ∃ q ∈ aperyStandardSet m a b c hm hgcd,
      aperyWeight a b c p = aperyWeight a b c q + h*m ∧
      aperyKey a b c q < aperyKey a b c p := by
  let q := aperyRepresentative m a b c hm hgcd
    (residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p)
  have hq := aperyRepresentative_spec m a b c hm hgcd
    (residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p)
  have hmem : q ∈ aperyStandardSet m a b c hm hgcd :=
    (mem_aperyStandardSet m a b c hm hgcd q).mpr hq.2
  have hle := aperyCanonical_weight_min m a b c hq.2 hq.1.symm
  have he : (aperyWeight a b c p : ZMod m) = (aperyWeight a b c q : ZMod m) := by
    rw [aperyWeight_cast, aperyWeight_cast]
    exact hq.1.symm
  obtain ⟨h, hh⟩ := nat_eq_add_mul_of_cast_eq m _ _ hle he
  refine ⟨h,q,hmem,hh,lt_of_le_of_ne (hq.2 p hq.1.symm) ?_⟩
  intro hk
  have heq : q = p := aperyKey_injective a b c hk
  exact hp.not_mem (heq ▸ hmem)

abbrev PresentationBorder (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :=
  {p : Point3 // MinimalComplement (aperyStandardSet m a b c hm hgcd) p}

noncomputable def boundaryReplacement (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (p : PresentationBorder m a b c hm hgcd) : Fact4 :=
  (Classical.choose (presentation_border_replacement m a b c hm hgcd p.1 p.2),
    Classical.choose (Classical.choose_spec (presentation_border_replacement m a b c hm hgcd p.1 p.2)))

theorem boundaryReplacement_spec (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (p : PresentationBorder m a b c hm hgcd) :
    (boundaryReplacement m a b c hm hgcd p).2 ∈ aperyStandardSet m a b c hm hgcd ∧
    aperyWeight a b c p.1 = aperyWeight a b c (boundaryReplacement m a b c hm hgcd p).2 +
      (boundaryReplacement m a b c hm hgcd p).1*m ∧
    aperyKey a b c (boundaryReplacement m a b c hm hgcd p).2 < aperyKey a b c p.1 :=
  Classical.choose_spec (Classical.choose_spec (presentation_border_replacement m a b c hm hgcd p.1 p.2))

noncomputable def boundaryRelations (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) : Finset (Fact4 × Fact4) := by
  classical
  letI : Finite (PresentationBorder m a b c hm hgcd) :=
    minimalComplement_finite (aperyCyclicStaircase m a b c hm hgcd)
  letI := Fintype.ofFinite (PresentationBorder m a b c hm hgcd)
  exact Finset.univ.image (fun p => ((0,p.1),boundaryReplacement m a b c hm hgcd p))

theorem boundaryRelations_edge_mem (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (p : PresentationBorder m a b c hm hgcd) :
    ((0,p.1),boundaryReplacement m a b c hm hgcd p) ∈ boundaryRelations m a b c hm hgcd := by
  classical
  letI : Finite (PresentationBorder m a b c hm hgcd) :=
    minimalComplement_finite (aperyCyclicStaircase m a b c hm hgcd)
  letI := Fintype.ofFinite (PresentationBorder m a b c hm hgcd)
  unfold boundaryRelations
  exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩

theorem boundaryRelations_sound (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    ∀ e ∈ boundaryRelations m a b c hm hgcd,
      factorWeight m a b c e.1 = factorWeight m a b c e.2 := by
  classical
  intro e he
  unfold boundaryRelations at he
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp he
  have hs := (boundaryReplacement_spec m a b c hm hgcd p).2.1
  simpa only [factorWeight, zero_mul, zero_add, Nat.add_comm] using hs

theorem boundaryRelations_card (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    (boundaryRelations m a b c hm hgcd).card ≤ Nat.card (PresentationBorder m a b c hm hgcd) := by
  classical
  letI : Finite (PresentationBorder m a b c hm hgcd) :=
    minimalComplement_finite (aperyCyclicStaircase m a b c hm hgcd)
  letI := Fintype.ofFinite (PresentationBorder m a b c hm hgcd)
  unfold boundaryRelations
  exact (Finset.card_image_le).trans_eq (by rw [Finset.card_univ, Nat.card_eq_fintype_card])

end NSP3
