import NSP3.GeneratedSemigroupBasic

namespace NSP3

theorem generatedSemigroup_normal_form (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) (n : ℕ) :
    n ∈ generatedSemigroup m a b c ↔
      ∃ q ∈ aperyStandardSet m a b c hm hgcd, ∃ k : ℕ, n = aperyWeight a b c q+k*m := by
  constructor
  · intro hn
    obtain ⟨k,p,hp⟩ := (mem_generatedSemigroup_iff m a b c n).mp hn
    let q := aperyRepresentative m a b c hm hgcd
      (residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p)
    have hs := aperyRepresentative_spec m a b c hm hgcd
      (residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p)
    have hq : AperyCanonical m a b c q := hs.2
    have hle := aperyCanonical_weight_min m a b c hq hs.1.symm
    have he : (aperyWeight a b c p : ZMod m) = (aperyWeight a b c q : ZMod m) := by
      rw [aperyWeight_cast,aperyWeight_cast]
      exact hs.1.symm
    obtain ⟨j,hj⟩ := nat_eq_add_mul_of_cast_eq m _ _ hle he
    refine ⟨q,(mem_aperyStandardSet m a b c hm hgcd q).mpr hq,j+k,?_⟩
    rw [hp,hj]
    ring
  · rintro ⟨q,_,k,rfl⟩
    exact generatedSemigroup_add m a b c (aperyWeight_mem_generatedSemigroup m a b c q)
      (generatedSemigroup_mul_mem m a b c k)

theorem canonical_weight_mem_generatedApery (m a b c : ℕ) (hm : 0 < m)
    {q : Point3} (hq : AperyCanonical m a b c q) :
    aperyWeight a b c q ∈ generatedApery m a b c := by
  refine ⟨aperyWeight_mem_generatedSemigroup m a b c q,?_⟩
  by_cases hlt : aperyWeight a b c q < m
  · exact Or.inl hlt
  · refine Or.inr ?_
    intro hpred
    obtain ⟨k,u,hu⟩ := (mem_generatedSemigroup_iff m a b c _).mp hpred
    have hge : m ≤ aperyWeight a b c q := Nat.le_of_not_gt hlt
    have hw : aperyWeight a b c q = (k+1)*m + aperyWeight a b c u := by
      calc
        aperyWeight a b c q = (aperyWeight a b c q-m)+m := (Nat.sub_add_cancel hge).symm
        _ = (k+1)*m + aperyWeight a b c u := by rw [hu]; ring
    have hz := congrArg (fun n : ℕ => (n : ZMod m)) hw
    push_cast at hz
    simp only [ZMod.natCast_self,mul_zero,zero_add] at hz
    have hr : residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) u =
        residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q := by
      rw [← aperyWeight_cast,← aperyWeight_cast]
      exact hz.symm
    have hle := aperyCanonical_weight_min m a b c hq hr
    nlinarith

theorem generatedApery_eq_weights (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    generatedApery m a b c =
      {n : ℕ | ∃ q ∈ aperyStandardSet m a b c hm hgcd, n = aperyWeight a b c q} := by
  ext n
  constructor
  · intro hn
    obtain ⟨q,hq,k,hk⟩ := (generatedSemigroup_normal_form m a b c hm hgcd n).mp hn.1
    have hk0 : k=0 := by
      by_contra hne
      have hkpos : 1 ≤ k := by omega
      have he : k=(k-1)+1 := by omega
      have hge : m ≤ n := by nlinarith
      have hpred : n-m = aperyWeight a b c q+(k-1)*m := by
        rw [he] at hk
        nlinarith [Nat.sub_add_cancel hge]
      have hmem : n-m ∈ generatedSemigroup m a b c := by
        rw [hpred]
        exact generatedSemigroup_add m a b c (aperyWeight_mem_generatedSemigroup m a b c q)
          (generatedSemigroup_mul_mem m a b c (k-1))
      rcases hn.2 with hsmall | hnot
      · omega
      · exact hnot hmem
    refine ⟨q,hq,?_⟩
    simpa [hk0] using hk
  · rintro ⟨q,hq,rfl⟩
    exact canonical_weight_mem_generatedApery m a b c hm
      ((mem_aperyStandardSet m a b c hm hgcd q).mp hq)

/-- Exact original numeric set equality; no multiplicity or minimality assumption. -/
theorem generated_semigroup_apery_weight_set (m a b c : ℕ) (hm : 0 < m)
    (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    {n : ℕ | (∃ k x y z : ℕ, n = k*m + a*x + b*y + c*z) ∧
      (n < m ∨ ¬ ∃ k x y z : ℕ, n-m = k*m + a*x + b*y + c*z)} =
    {n : ℕ | ∃ q ∈ aperyStandardSet m a b c hm hgcd, n = aperyWeight a b c q} :=
  generatedApery_eq_weights m a b c hm hgcd

end NSP3
