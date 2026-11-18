import P3TorSpike.SemigroupRing

noncomputable section
namespace NSP3.TorSpike

def polynomialEmbedding (k : Type) [Field k] (m a b c : ℕ) :
    SemigroupRing k m a b c →ₐ[k] Polynomial k :=
  (Polynomial.toFinsuppIsoAlg k).symm.toAlgHom.comp
    (AddMonoidAlgebra.mapDomainAlgHom k k (Semigroup m a b c).subtype)

def augmentation (k : Type) [Field k] (m a b c : ℕ) :
    SemigroupRing k m a b c →ₐ[k] k :=
  (Polynomial.aeval (0:k)).comp (polynomialEmbedding k m a b c)

theorem polynomialEmbedding_monomial (k : Type) [Field k] (m a b c : ℕ)
    (s : Semigroup m a b c) :
    polynomialEmbedding k m a b c (monomial k s)=Polynomial.monomial s.val 1 := by
  simp [polynomialEmbedding,monomial,AddMonoidAlgebra.mapDomainAlgHom,
    Polynomial.toFinsuppIsoAlg,Polynomial.toFinsuppIso]
  rfl

@[simp] theorem augmentation_monomial (k : Type) [Field k] (m a b c : ℕ)
    (s : Semigroup m a b c) :
    augmentation k m a b c (monomial k s)=(if s.val=0 then 1 else 0) := by
  simp [augmentation,polynomialEmbedding_monomial]
  by_cases hz : s=0
  · subst s
    simp
  · have hv : s.val≠0 := fun h => hz (Subtype.ext h)
    simp [hz,zero_pow hv]

theorem augmentation_polynomialMap (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    (augmentation k m a b c).comp (polynomialMap k m a b c)=
      MvPolynomial.aeval (fun _ : Fin 4 => (0:k)) := by
  ext i
  simp only [AlgHom.comp_apply,polynomialMap_X,MvPolynomial.aeval_X]
  rw [augmentation_monomial]
  have hm := h.positive
  have ha := h.least_a
  have hb := h.least_b
  have hc := h.least_c
  have hpos : 0 < (generator m a b c i).val := by
    fin_cases i <;> simp [generator] <;> omega
  simp [Nat.ne_of_gt hpos]

theorem augmentation_surjective (k : Type) [Field k] (m a b c : ℕ) :
    Function.Surjective (augmentation k m a b c) := by
  intro r
  exact ⟨algebraMap k (SemigroupRing k m a b c) r,(augmentation k m a b c).commutes r⟩

end NSP3.TorSpike
