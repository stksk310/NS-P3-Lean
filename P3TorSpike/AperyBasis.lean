import P3TorSpike.ArtinianReduction

noncomputable section
namespace NSP3.TorSpike

def coefficient (k : Type) [Field k] {m a b c : ℕ} (s : Semigroup m a b c) :
    SemigroupRing k m a b c →ₗ[k] k :=
  (Finsupp.lapply s).comp (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap

theorem ideal_coefficient_zero (k : Type) [Field k] (m a b c : ℕ)
    (s : Semigroup m a b c) (hs : s.val ∈ generatedApery m a b c)
    (f : SemigroupRing k m a b c) (hf : f ∈ multiplicityIdeal k m a b c) :
    coefficient k s f=0 := by
  obtain ⟨g,rfl⟩ := Ideal.mem_span_singleton.mp hf
  change (AddMonoidAlgebra.single (generator m a b c 0) (1:k)*g).coeff s=0
  apply AddMonoidAlgebra.coeff_single_mul_of_forall_add_ne
  intro d he
  have hn : m+d.val=s.val := congrArg Subtype.val he
  rcases hs.2 with hsmall | hgap
  · omega
  · apply hgap
    have hd : s.val-m=d.val := by omega
    rw [hd]
    exact d.property

def aperyExponent (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1)
    (p : AperyIndex m a b c hm hgcd) : Semigroup m a b c :=
  ⟨aperyWeight a b c p.val,aperyWeight_mem_generatedSemigroup m a b c p.val⟩

theorem aperyExponent_injective (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    Function.Injective (aperyExponent m a b c hm hgcd) := by
  intro p q he
  have hw := congrArg Subtype.val he
  change aperyWeight a b c p.val=aperyWeight a b c q.val at hw
  apply Subtype.ext
  apply aperyCanonical_unique m a b c
    ((mem_aperyStandardSet m a b c hm hgcd p.val).mp p.property)
    ((mem_aperyStandardSet m a b c hm hgcd q.val).mp q.property)
  rw [← aperyWeight_cast,← aperyWeight_cast,hw]

theorem aperyVectors_independent (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    LinearIndependent k (aperyVector k m a b c hm hgcd) := by
  classical
  apply linearIndependent_iff'.mpr
  intro F r hrel p hp
  let raw := fun q : AperyIndex m a b c hm hgcd => monomial k (aperyExponent m a b c hm hgcd q)
  let f := ∑ q ∈ F, r q • raw q
  have hmk : reductionMap k m a b c f=0 := by
    simpa only [f,raw,map_sum,map_smul,aperyVector,aperyExponent] using hrel
  have hmem : f ∈ multiplicityIdeal k m a b c := Ideal.Quotient.eq_zero_iff_mem.mp hmk
  have hap : (aperyExponent m a b c hm hgcd p).val ∈ generatedApery m a b c :=
    canonical_weight_mem_generatedApery m a b c hm
      ((mem_aperyStandardSet m a b c hm hgcd p.val).mp p.property)
  have hz := ideal_coefficient_zero k m a b c (aperyExponent m a b c hm hgcd p) hap f hmem
  have hdelta (q : AperyIndex m a b c hm hgcd) :
      coefficient k (aperyExponent m a b c hm hgcd p) (raw q)=(if q=p then 1 else 0) := by
    change (monomial k (aperyExponent m a b c hm hgcd q)).coeff
      (aperyExponent m a b c hm hgcd p)=_
    simp [monomial,Finsupp.single_apply,
      (aperyExponent_injective m a b c hm hgcd).eq_iff]
  change coefficient k (aperyExponent m a b c hm hgcd p) (∑ q ∈ F,r q • raw q)=0 at hz
  simp only [map_sum,map_smul,hdelta,smul_eq_mul,mul_ite,mul_one,mul_zero] at hz
  simpa [hp] using hz

def aperyBasis (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    Module.Basis (AperyIndex m a b c hm hgcd) k (Reduction k m a b c) :=
  Module.Basis.mk (aperyVectors_independent k m a b c hm hgcd)
    (by rw [aperyVectors_span])

theorem reduction_finrank_eq_m (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    Module.finrank k (Reduction k m a b c)=m := by
  classical
  have h := Module.finrank_eq_card_basis (aperyBasis k m a b c hm hgcd)
  have hc : Fintype.card (AperyIndex m a b c hm hgcd)=m := by
    simpa only [Fintype.card_coe] using aperyStandardSet_card m a b c hm hgcd
  exact h.trans hc

end NSP3.TorSpike
