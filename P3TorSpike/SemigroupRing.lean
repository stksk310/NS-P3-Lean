import NSP3.V03

noncomputable section
namespace NSP3.TorSpike

abbrev Semigroup (m a b c : ℕ) := generatedAddSubmonoid m a b c
abbrev SemigroupRing (k : Type) [Field k] (m a b c : ℕ) :=
  AddMonoidAlgebra k (Semigroup m a b c)
abbrev PolynomialRing (k : Type) [Field k] := MvPolynomial (Fin 4) k

def generator (m a b c : ℕ) (i : Fin 4) : Semigroup m a b c :=
  ![⟨m,(generatedSemigroup_generators m a b c).1⟩,
    ⟨a,(generatedSemigroup_generators m a b c).2.1⟩,
    ⟨b,(generatedSemigroup_generators m a b c).2.2.1⟩,
    ⟨c,(generatedSemigroup_generators m a b c).2.2.2⟩] i

def monomial (k : Type) [Field k] {m a b c : ℕ} (s : Semigroup m a b c) :
    SemigroupRing k m a b c := AddMonoidAlgebra.single s 1

def polynomialMap (k : Type) [Field k] (m a b c : ℕ) :
    PolynomialRing k →ₐ[k] SemigroupRing k m a b c :=
  MvPolynomial.aeval (fun i => monomial k (generator m a b c i))

@[simp] theorem polynomialMap_X (k : Type) [Field k] (m a b c : ℕ) (i : Fin 4) :
    polynomialMap k m a b c (MvPolynomial.X i)=monomial k (generator m a b c i) :=
  MvPolynomial.aeval_X _ _

theorem monomial_factorization (k : Type) [Field k] (m a b c : ℕ)
    (s : Semigroup m a b c) (t x y z : ℕ)
    (hs : s.val=t*m+a*x+b*y+c*z) :
    monomial k s = monomial k (generator m a b c 0)^t *
      monomial k (generator m a b c 1)^x *
      monomial k (generator m a b c 2)^y *
      monomial k (generator m a b c 3)^z := by
  simp only [monomial,AddMonoidAlgebra.single_pow,one_pow,
    AddMonoidAlgebra.single_mul_single,mul_one]
  congr 1
  apply Subtype.ext
  simpa [generator,add_comm,add_left_comm,add_assoc,mul_comm] using hs

theorem monomial_in_range (k : Type) [Field k] (m a b c : ℕ) (s : Semigroup m a b c) :
    monomial k s ∈ (polynomialMap k m a b c).range := by
  obtain ⟨t,x,y,z,hs⟩ := s.property
  refine ⟨MvPolynomial.X 0^t * MvPolynomial.X 1^x *
    MvPolynomial.X 2^y * MvPolynomial.X 3^z,?_⟩
  change polynomialMap k m a b c (MvPolynomial.X 0^t * MvPolynomial.X 1^x *
    MvPolynomial.X 2^y * MvPolynomial.X 3^z)=monomial k s
  simp only [map_mul,map_pow,polynomialMap_X]
  exact (monomial_factorization k m a b c s t x y z hs).symm

theorem polynomialMap_surjective (k : Type) [Field k] (m a b c : ℕ) :
    Function.Surjective (polynomialMap k m a b c) := by
  intro f
  change f∈(polynomialMap k m a b c).range
  induction f using AddMonoidAlgebra.induction_on with
  | of s => exact monomial_in_range k m a b c s
  | add f g hf hg => exact (polynomialMap k m a b c).range.add_mem hf hg
  | smul r f hf => exact (polynomialMap k m a b c).range.smul_mem hf r

theorem monomial_ne_zero (k : Type) [Field k] {m a b c : ℕ} (s : Semigroup m a b c) :
    monomial k s≠0 := by
  simp [monomial]

theorem monomial_mul_injective (k : Type) [Field k] {m a b c : ℕ}
    (s : Semigroup m a b c) :
    Function.Injective (fun f : SemigroupRing k m a b c => monomial k s*f) := by
  intro f g h
  exact mul_left_cancel₀ (monomial_ne_zero k s) h

end NSP3.TorSpike
