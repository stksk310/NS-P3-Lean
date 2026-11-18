import P3TorSpike.AperyBasis
import NSP3.V03.BettiApery

noncomputable section
namespace NSP3.TorSpike
open NSP3.V03

def nonmultiplicityGenerator (m a b c : ℕ) (i : Fin 3) : Semigroup m a b c :=
  ![generator m a b c 1, generator m a b c 2, generator m a b c 3] i

def reducedGenerator (k : Type) [Field k] (m a b c : ℕ) (i : Fin 3) : Reduction k m a b c :=
  reductionMap k m a b c (monomial k (nonmultiplicityGenerator m a b c i))

/-- The actual simultaneous annihilator of the three nonmultiplicity monomials. -/
def socle (k : Type) [Field k] (m a b c : ℕ) : Submodule k (Reduction k m a b c) where
  carrier := {f | ∀ i : Fin 3, reducedGenerator k m a b c i * f = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg i; rw [mul_add, hf i, hg i, add_zero]
  smul_mem' := by intro r f hf i; rw [mul_smul_comm, hf i, smul_zero]

@[simp] theorem mem_socle (k : Type) [Field k] (m a b c : ℕ) (f : Reduction k m a b c) :
    f ∈ socle k m a b c ↔ ∀ i : Fin 3, reducedGenerator k m a b c i * f = 0 := Iff.rfl

@[simp] theorem aperyBasis_apply (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (p : AperyIndex m a b c hm hgcd) :
    aperyBasis k m a b c hm hgcd p = aperyVector k m a b c hm hgcd p := by
  simp [aperyBasis]

theorem reduced_mul_aperyVector (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (s : Semigroup m a b c) (p : AperyIndex m a b c hm hgcd) :
    reductionMap k m a b c (monomial k s) * aperyVector k m a b c hm hgcd p =
      reductionMap k m a b c (monomial k (s + aperyExponent m a b c hm hgcd p)) := by
  rw [monomial_add,map_mul]
  rfl

/-- A surviving weight shift detects exactly one input coefficient. -/
theorem annihilated_coordinate_zero (k : Type) [Field k] (m a b c : ℕ)
    (hm : 0 < m) (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (s : Semigroup m a b c) (f : Reduction k m a b c)
    (hf : reductionMap k m a b c (monomial k s) * f = 0)
    (p : AperyIndex m a b c hm hgcd)
    (hp : (s + aperyExponent m a b c hm hgcd p).val ∈ generatedApery m a b c) :
    (aperyBasis k m a b c hm hgcd).repr f p = 0 := by
  classical
  let B := aperyBasis k m a b c hm hgcd
  let raw := fun q : AperyIndex m a b c hm hgcd =>
    monomial k (s + aperyExponent m a b c hm hgcd q)
  let F := ∑ q, B.repr f q • raw q
  have hF : reductionMap k m a b c F = 0 := by
    change reductionMap k m a b c (∑ q, B.repr f q • raw q) = 0
    simp only [map_sum,map_smul]
    simp only [raw, ← reduced_mul_aperyVector, ← aperyBasis_apply, ← mul_smul_comm,
      ← Finset.mul_sum]
    rw [Module.Basis.sum_repr]
    exact hf
  have hmem : F ∈ multiplicityIdeal k m a b c := Ideal.Quotient.eq_zero_iff_mem.mp hF
  have hz := ideal_coefficient_zero k m a b c
    (s + aperyExponent m a b c hm hgcd p) hp F hmem
  have hdelta (q : AperyIndex m a b c hm hgcd) :
      coefficient k (s + aperyExponent m a b c hm hgcd p) (raw q) =
        (if q = p then 1 else 0) := by
    change (monomial k (s + aperyExponent m a b c hm hgcd q)).coeff
      (s + aperyExponent m a b c hm hgcd p) = _
    have he : (s + aperyExponent m a b c hm hgcd q =
        s + aperyExponent m a b c hm hgcd p) ↔ q = p := by
      rw [add_left_cancel_iff]
      exact (aperyExponent_injective m a b c hm hgcd).eq_iff
    simp [monomial,Finsupp.single_apply,he]
  change coefficient k (s + aperyExponent m a b c hm hgcd p)
    (∑ q, B.repr f q • raw q) = 0 at hz
  simpa only [map_sum,map_smul,hdelta,smul_eq_mul,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hz

theorem terminal_iff_all_shift_not_apery (m a b c : ℕ) (n : ℕ)
    (hn : n ∈ generatedApery m a b c) :
    TerminalApery m a b c n ↔ ∀ i : Fin 3,
      (nonmultiplicityGenerator m a b c i).val + n ∉ generatedApery m a b c := by
  constructor
  · intro ht i
    fin_cases i
    · simpa [nonmultiplicityGenerator,generator,add_comm] using ht.2.1
    · simpa [nonmultiplicityGenerator,generator,add_comm] using ht.2.2.1
    · simpa [nonmultiplicityGenerator,generator,add_comm] using ht.2.2.2
  · intro ht
    exact ⟨hn,by simpa [nonmultiplicityGenerator,generator,add_comm] using ht 0,
      by simpa [nonmultiplicityGenerator,generator,add_comm] using ht 1,
      by simpa [nonmultiplicityGenerator,generator,add_comm] using ht 2⟩

end NSP3.TorSpike
