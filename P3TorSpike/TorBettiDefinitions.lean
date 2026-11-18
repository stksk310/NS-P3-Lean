import P3TorSpike.TorZero
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

noncomputable section
namespace NSP3.TorSpike
open CategoryTheory

/-- Total Betti number defined from the actual categorical Tor object.
Finiteness is proved separately before using this numerical invariant. -/
def torBetti (k : Type) [Field k] (m a b c n : ℕ) : ℕ :=
  Module.finrank k ((ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
    (torModule k m a b c n))

theorem torBetti_eq_finrank (k : Type) [Field k] (m a b c n : ℕ)
    (M : ModuleCat.{0} k)
    (e : (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
      (torModule k m a b c n) ≅ M) : torBetti k m a b c n = Module.finrank k M :=
  e.toLinearEquiv.finrank_eq

theorem tor_finite_of_iso (k : Type) [Field k] (m a b c n : ℕ)
    (M : ModuleCat.{0} k) [Module.Finite k M]
    (e : (ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
      (torModule k m a b c n) ≅ M) :
    Module.Finite k ((ModuleCat.restrictScalars (algebraMap k (PolynomialRing k))).obj
      (torModule k m a b c n)) :=
  Module.Finite.of_surjective e.symm.toLinearEquiv.toLinearMap e.symm.toLinearEquiv.surjective

theorem torBetti_zero (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) : torBetti k m a b c 0 = 1 :=
  torFinrank_zero k m a b c h

end NSP3.TorSpike
