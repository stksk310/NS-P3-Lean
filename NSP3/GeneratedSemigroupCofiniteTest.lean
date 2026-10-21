import NSP3.GeneratedSemigroupCofinite

namespace NSP3
-- Catches assuming rather than proving finite complement of the actual numeric Γ.
example (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    (generatedSemigroup m a b c)ᶜ.Finite :=
  generatedSemigroup_cofinite m a b c hm hgcd

-- Catches confusing numeric Apéry cardinality with staircase boundary cardinality.
example (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    (generatedApery m a b c).ncard = m :=
  generatedApery_ncard m a b c hm hgcd

-- m=1 and repeated redundant weights: actual Apéry has only its zero residue.
example : (generatedApery 1 7 7 7).ncard = 1 :=
  generatedApery_ncard 1 7 7 7 (by norm_num) (by norm_num)

-- Composite modulus; none of the three other generators is a unit.
example : (generatedSemigroup 30 6 10 15)ᶜ.Finite :=
  generatedSemigroup_cofinite 30 6 10 15 (by norm_num) (by norm_num)

-- m is not the multiplicity and c duplicates m; no e=4 inference is allowed.
example : (generatedApery 4 2 3 4).ncard = 4 :=
  generatedApery_ncard 4 2 3 4 (by norm_num) (by norm_num)

-- Dropping the n<m guard would wrongly exclude 0 since truncated 0-m=0 is in Γ.
example (m a b c : ℕ) (hm : 0 < m) : 0 ∈ generatedApery m a b c :=
  ⟨generatedSemigroup_zero m a b c,Or.inl hm⟩

example : 5 ∈ generatedApery 4 2 3 4 := by
  refine ⟨⟨0,1,1,0,by norm_num⟩,Or.inr ?_⟩
  rintro ⟨k,x,y,z,h⟩
  norm_num at h
  omega
end NSP3
