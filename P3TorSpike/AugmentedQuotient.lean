import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
namespace NSP3.TorSpike

/-- A polynomially generated augmented algebra modulo all its variable images
is its coefficient field. The hypotheses are structural, not dimension claims. -/
def variablesQuotientEquiv (k A : Type) [Field k] [CommRing A] [Algebra k A]
    (f : MvPolynomial (Fin 4) k →ₐ[k] A) (hs : Function.Surjective f)
    (ε : A →ₐ[k] k) (J : Ideal A)
    (hJ : ∀ x ∈ J, ε x = 0)
    (hX : ∀ i, f (MvPolynomial.X i) ∈ J) : (A ⧸ J) ≃ₐ[k] k := by
  let e : (A ⧸ J) →ₐ[k] k := Ideal.Quotient.liftₐ J ε hJ
  let q : A →ₐ[k] (A ⧸ J) := Ideal.Quotient.mkₐ k J
  have hf : q.comp f =
      (Algebra.ofId k (A ⧸ J)).comp (MvPolynomial.aeval (fun _ : Fin 4 => (0 : k))) := by
    ext i
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hX i)
  have hleft : Function.LeftInverse (algebraMap k (A ⧸ J)) e := by
    intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J x
    obtain ⟨p, rfl⟩ := hs y
    have hp := DFunLike.congr_fun hf p
    change q (f p) = _ at hp
    have hε : e (q (f p)) =
        (MvPolynomial.aeval (fun _ : Fin 4 => (0 : k))) p := by
      rw [hp]
      exact e.commutes _
    change algebraMap k (A ⧸ J) (e (q (f p))) = q (f p)
    rw [hε]
    exact hp.symm
  have hright : Function.RightInverse (algebraMap k (A ⧸ J)) e := by
    intro r
    exact e.commutes r
  exact AlgEquiv.ofBijective e ⟨hleft.injective, hright.surjective⟩

end NSP3.TorSpike
