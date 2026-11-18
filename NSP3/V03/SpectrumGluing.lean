import NSP3.V03.SpectrumRank

namespace NSP3.V03

/-- A base normalization and one gluing edge normalize the first coefficient modulo A. -/
theorem normalize_gluing_coefficient (R : Finset (Fact4 × Fact4)) (A : ℕ)
    (hA : 0<A) (p : Point3) (P : Point3 → Prop)
    (hbase : ∀ t q, ∃ r, P r ∧ PresentationRel R (t,q) (t,r))
    (hglue : ((A,⟨0,0,0⟩),(0,p)) ∈ R) (t : ℕ) (q : Point3) :
    ∃ T r, T<A ∧ P r ∧ PresentationRel R (t,q) (T,r) := by
  induction t using Nat.strong_induction_on generalizing q with
  | h t ih =>
    by_cases ht : t<A
    · obtain ⟨r,hr,he⟩ := hbase t q
      exact ⟨t,r,ht,hr,he⟩
    · have hedge := PresentationRel.context (PresentationRel.edge hglue) (t-A,q)
      have he : PresentationRel R (t,q) (t-A,p+q) := by
        change PresentationRel R (A+(t-A),(⟨0,0,0⟩ : Point3)+q) (0+(t-A),p+q) at hedge
        have hc : A+(t-A)=t := by omega
        have hz : (⟨0,0,0⟩ : Point3)+q=q := by ext <;> simp
        simpa only [hc,hz,Nat.zero_add] using hedge
      obtain ⟨T,r,hT,hr,hrel⟩ := ih (t-A) (by omega) (p+q)
      exact ⟨T,r,hT,hr,PresentationRel.trans he hrel⟩

/-- The m coefficient is unique in [0,m] after a gluing by the coprime scale m+1. -/
theorem gluing_coefficient_eq (m t u B C : ℕ) (ht : t < m + 1) (hu : u < m + 1)
    (he : t*m+(m+1)*B=u*m+(m+1)*C) : t=u := by
  have he' : (t : ℤ)*m+(m+1)*B=(u : ℤ)*m+(m+1)*C := by exact_mod_cast he
  have hd : ((m+1 : ℕ) : ℤ) ∣ (t : ℤ)-u := by
    refine ⟨(t : ℤ)-u+B-C,?_⟩
    push_cast
    nlinarith [he']
  obtain ⟨k,hk⟩ := hd
  push_cast at hk
  have ht' : (t : ℤ)<(m : ℤ)+1 := by exact_mod_cast ht
  have hu' : (u : ℤ)<(m : ℤ)+1 := by exact_mod_cast hu
  have ht0 : (0 : ℤ) ≤ t := by omega
  have hu0 : (0 : ℤ) ≤ u := by omega
  have hm0 : (0 : ℤ) ≤ m := by omega
  by_cases hz : k=0
  · simp [hz] at hk
    omega
  · by_cases hp : 0<k
    · have : 1≤k := by omega
      nlinarith
    · have : k≤-1 := by omega
      nlinarith

end NSP3.V03
