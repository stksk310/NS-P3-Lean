import NSP3.SimplexPolynomial

namespace NSP3

example : simplexCard 0 0 = 0 := by native_decide
example : simplexCard 4 1 = 0 := by native_decide
example : simplexCard 4 2 = 3 := by native_decide
example : simplexCard 4 4 = 10 := by native_decide

example (s t : ℕ) (hst : t ≤ s) :
    6 * simplexCard s t = t * (t - 1) * (3 * s - 2 * t + 1) :=
  six_mul_simplexCard s t hst

end NSP3
