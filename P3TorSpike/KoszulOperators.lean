import P3TorSpike.TorObjects
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section
namespace NSP3.TorSpike.Koszul
open MvPolynomial
variable {k : Type} [Field k]

/-- Division by a coordinate monomial, defined over every field. -/
def quotient (i : Fin 4) (p : PolynomialRing k) : PolynomialRing k :=
  p.divMonomial (Finsupp.single i 1)

/-- The complementary coordinate-zero projection. -/
def remainder (i : Fin 4) (p : PolynomialRing k) : PolynomialRing k :=
  p - X i * quotient i p

@[simp] theorem quotient_zero (i : Fin 4) : quotient i (0 : PolynomialRing k) = 0 := by
  simp [quotient]
@[simp] theorem quotient_add (i : Fin 4) (p q : PolynomialRing k) :
    quotient i (p + q) = quotient i p + quotient i q := by
  exact add_divMonomial _ _ _
@[simp] theorem quotient_neg (i : Fin 4) (p : PolynomialRing k) :
    quotient i (-p) = -quotient i p := by
  apply eq_neg_of_add_eq_zero_left
  rw [← quotient_add, neg_add_cancel, quotient_zero]
@[simp] theorem quotient_sub (i : Fin 4) (p q : PolynomialRing k) :
    quotient i (p - q) = quotient i p - quotient i q := by
  simp [sub_eq_add_neg]
@[simp] theorem quotient_X_mul (i : Fin 4) (p : PolynomialRing k) :
    quotient i (X i * p) = p := by
  exact X_mul_divMonomial i p

@[simp] theorem quotient_X_mul_ne (i j : Fin 4) (h : i ≠ j) (p : PolynomialRing k) :
    quotient i (X j * p) = X j * quotient i p := by
  ext d
  simp only [quotient, coeff_divMonomial, coeff_X_mul', Finsupp.mem_support_iff]
  have hij : ((Finsupp.single i 1 : Fin 4 →₀ ℕ) + d) j = d j := by simp [h]
  rw [hij]
  split_ifs with hd
  · congr 1
    ext a
    by_cases ha : a = i
    · subst a
      simp [h, Finsupp.sub_apply]
    · by_cases haj : a = j
      · subst a
        simp [Ne.symm h, Finsupp.sub_apply]
      · simp [ha, haj, Finsupp.sub_apply]
  · rfl

@[simp] theorem remainder_zero (i : Fin 4) : remainder i (0 : PolynomialRing k) = 0 := by
  simp [remainder]
@[simp] theorem remainder_add (i : Fin 4) (p q : PolynomialRing k) :
    remainder i (p + q) = remainder i p + remainder i q := by
  simp [remainder, mul_add]; ring
@[simp] theorem remainder_neg (i : Fin 4) (p : PolynomialRing k) :
    remainder i (-p) = -remainder i p := by
  simp [remainder]; ring
@[simp] theorem remainder_sub (i : Fin 4) (p q : PolynomialRing k) :
    remainder i (p - q) = remainder i p - remainder i q := by
  simp [sub_eq_add_neg]
@[simp] theorem remainder_X_mul (i : Fin 4) (p : PolynomialRing k) :
    remainder i (X i * p) = 0 := by
  simp [remainder]
@[simp] theorem remainder_X_mul_ne (i j : Fin 4) (h : i ≠ j) (p : PolynomialRing k) :
    remainder i (X j * p) = X j * remainder i p := by
  simp [remainder, quotient_X_mul_ne i j h]; ring

theorem quotient_remainder (i : Fin 4) (p : PolynomialRing k) :
    X i * quotient i p + remainder i p = p := by
  simp [remainder]

end NSP3.TorSpike.Koszul
