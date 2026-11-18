import P3TorSpike.SemigroupRing

noncomputable section
namespace NSP3.TorSpike

def multiplicityIdeal (k : Type) [Field k] (m a b c : ℕ) :
    Ideal (SemigroupRing k m a b c) :=
  Ideal.span {monomial k (generator m a b c 0)}

abbrev Reduction (k : Type) [Field k] (m a b c : ℕ) :=
  SemigroupRing k m a b c ⧸ multiplicityIdeal k m a b c

def reductionMap (k : Type) [Field k] (m a b c : ℕ) :
    SemigroupRing k m a b c →ₐ[k] Reduction k m a b c :=
  Ideal.Quotient.mkₐ k _

@[simp] theorem monomial_add (k : Type) [Field k] {m a b c : ℕ}
    (s t : Semigroup m a b c) : monomial k (s+t)=monomial k s*monomial k t := by
  simp [monomial,AddMonoidAlgebra.single_mul_single]

theorem outside_apery_killed (k : Type) [Field k] (m a b c : ℕ)
    (s : Semigroup m a b c) (hn : s.val ∉ generatedApery m a b c) :
    reductionMap k m a b c (monomial k s)=0 := by
  have hge : m ≤ s.val := by
    by_contra h
    exact hn ⟨s.property,Or.inl (by omega)⟩
  have hpred : s.val-m ∈ generatedSemigroup m a b c := by
    by_contra h
    exact hn ⟨s.property,Or.inr h⟩
  let t : Semigroup m a b c := ⟨s.val-m,hpred⟩
  have he : s=generator m a b c 0+t := by
    apply Subtype.ext
    change s.val=m+(s.val-m)
    omega
  change Ideal.Quotient.mk (multiplicityIdeal k m a b c) (monomial k s)=0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change monomial k s ∈ Ideal.span {monomial k (generator m a b c 0)}
  apply Ideal.mem_span_singleton.mpr
  exact ⟨monomial k t,by rw [he,monomial_add]⟩

abbrev AperyIndex (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :=
  {p : Point3 // p ∈ aperyStandardSet m a b c hm hgcd}

def aperyVector (k : Type) [Field k] (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) (p : AperyIndex m a b c hm hgcd) :
    Reduction k m a b c :=
  reductionMap k m a b c (monomial k
    ⟨aperyWeight a b c p.val,aperyWeight_mem_generatedSemigroup m a b c p.val⟩)

theorem reduced_monomial_in_apery_span (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1)
    (s : Semigroup m a b c) :
    reductionMap k m a b c (monomial k s) ∈ 
      Submodule.span k (Set.range (aperyVector k m a b c hm hgcd)) := by
  classical
  by_cases h : s.val ∈ generatedApery m a b c
  · rw [generatedApery_eq_weights m a b c hm hgcd] at h
    obtain ⟨p,hp,he⟩ := h
    apply Submodule.subset_span
    refine ⟨⟨p,hp⟩,?_⟩
    unfold aperyVector
    congr 2
    exact Subtype.ext he.symm
  · rw [outside_apery_killed k m a b c s h]
    exact Submodule.zero_mem _

theorem aperyVectors_span (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    Submodule.span k (Set.range (aperyVector k m a b c hm hgcd))=⊤ := by
  classical
  apply Submodule.eq_top_iff'.mpr
  intro f
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mkₐ_surjective k (multiplicityIdeal k m a b c) f
  change reductionMap k m a b c g ∈ _
  induction g using AddMonoidAlgebra.induction_on with
  | of s => exact reduced_monomial_in_apery_span k m a b c hm hgcd s
  | add g h hg hh => simpa only [map_add] using Submodule.add_mem _ hg hh
  | smul r g hg => simpa only [map_smul] using Submodule.smul_mem _ r hg

theorem reduction_finite (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    Module.Finite k (Reduction k m a b c) := by
  classical
  apply Module.Finite.of_fg_top
  rw [← aperyVectors_span k m a b c hm hgcd]
  exact Submodule.fg_span (Set.finite_range _)

theorem reduction_finrank_le_m (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    Module.finrank k (Reduction k m a b c) ≤ m := by
  classical
  have h := finrank_range_le_card (R := k) (aperyVector k m a b c hm hgcd)
  unfold Set.finrank at h
  rw [aperyVectors_span] at h
  have hc : Fintype.card (AperyIndex m a b c hm hgcd)=m := by
    simpa only [Fintype.card_coe] using aperyStandardSet_card m a b c hm hgcd
  simpa [hc] using h

end NSP3.TorSpike
