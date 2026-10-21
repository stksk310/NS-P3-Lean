import NSP3.GeneratedSemigroupApery

namespace NSP3

theorem aperyWeight_injOn_standardSet (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    Set.InjOn (aperyWeight a b c) (aperyStandardSet m a b c hm hgcd : Set Point3) := by
  intro p hp q hq he
  apply aperyCanonical_unique m a b c
    ((mem_aperyStandardSet m a b c hm hgcd p).mp hp)
    ((mem_aperyStandardSet m a b c hm hgcd q).mp hq)
  rw [← aperyWeight_cast,← aperyWeight_cast,he]

theorem generatedApery_eq_finset (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    generatedApery m a b c =
      ((aperyStandardSet m a b c hm hgcd).image (aperyWeight a b c) : Set ℕ) := by
  rw [generatedApery_eq_weights m a b c hm hgcd]
  ext n
  simp only [Set.mem_ofPred_eq,Finset.mem_coe,Finset.mem_image]
  constructor
  · rintro ⟨q,hq,hn⟩
    exact ⟨q,hq,hn.symm⟩
  · rintro ⟨q,hq,hn⟩
    exact ⟨q,hq,hn.symm⟩

theorem generatedApery_finite (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    (generatedApery m a b c).Finite := by
  rw [generatedApery_eq_finset m a b c hm hgcd]
  exact Finset.finite_toSet _

theorem generatedApery_ncard (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    (generatedApery m a b c).ncard = m := by
  rw [generatedApery_eq_finset m a b c hm hgcd,Set.ncard_coe_finset,
    Finset.card_image_of_injOn (aperyWeight_injOn_standardSet m a b c hm hgcd)]
  exact aperyStandardSet_card m a b c hm hgcd

/-- An explicit upper bound for a conductor, not a claim of optimality. -/
noncomputable def generatedConductorBound (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) : ℕ :=
  (aperyStandardSet m a b c hm hgcd).sup (aperyWeight a b c)

theorem generatedSemigroup_above_conductor (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) {n : ℕ}
    (hn : generatedConductorBound m a b c hm hgcd ≤ n) :
    n ∈ generatedSemigroup m a b c := by
  let q := aperyRepresentative m a b c hm hgcd (n : ZMod m)
  have hs := aperyRepresentative_spec m a b c hm hgcd (n : ZMod m)
  have hq : q ∈ aperyStandardSet m a b c hm hgcd :=
    (mem_aperyStandardSet m a b c hm hgcd q).mpr hs.2
  have hw : aperyWeight a b c q ≤ generatedConductorBound m a b c hm hgcd :=
    Finset.le_sup hq
  have he : (n : ZMod m) = (aperyWeight a b c q : ZMod m) := by
    rw [aperyWeight_cast]
    exact hs.1.symm
  obtain ⟨k,hk⟩ := nat_eq_add_mul_of_cast_eq m n _ (hw.trans hn) he
  exact (generatedSemigroup_normal_form m a b c hm hgcd n).mpr ⟨q,hq,k,hk⟩

theorem generatedSemigroup_cofinite (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    (generatedSemigroup m a b c)ᶜ.Finite := by
  refine (Finset.range (generatedConductorBound m a b c hm hgcd)).finite_toSet.subset ?_
  intro n hn
  apply Finset.mem_coe.mpr
  apply Finset.mem_range.mpr
  by_contra h
  exact hn (generatedSemigroup_above_conductor m a b c hm hgcd (by omega))

end NSP3
