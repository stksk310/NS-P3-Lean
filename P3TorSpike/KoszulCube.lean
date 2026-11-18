import P3TorSpike.KoszulOperators

noncomputable section
namespace NSP3.TorSpike.Koszul
open MvPolynomial
variable {k : Type} [Field k]

/-- Exterior basis in binary order: bit i records the presence of e_i. -/
abbrev Cube (k : Type) [Field k] := Fin 16 → PolynomialRing k

/-- The signed four-coordinate Koszul differential, simultaneously in all degrees. -/
def differential (v : Cube k) : Cube k := ![
  X 0*v 1 + X 1*v 2 + X 2*v 4 + X 3*v 8,
  -X 1*v 3 - X 2*v 5 - X 3*v 9,
  X 0*v 3 - X 2*v 6 - X 3*v 10,
  X 2*v 7 + X 3*v 11,
  X 0*v 5 + X 1*v 6 - X 3*v 12,
  -X 1*v 7 + X 3*v 13,
  X 0*v 7 + X 3*v 14,
  -X 3*v 15,
  X 0*v 9 + X 1*v 10 + X 2*v 12,
  -X 1*v 11 - X 2*v 13,
  X 0*v 11 - X 2*v 14,
  X 2*v 15,
  X 0*v 13 + X 1*v 14,
  -X 1*v 15,
  X 0*v 15,
  0]

@[simp] theorem differential_zero : differential (0 : Cube k) = 0 := by
  funext i; fin_cases i <;> simp [differential]

theorem differential_add (v w : Cube k) :
    differential (v + w) = differential v + differential w := by
  funext i; fin_cases i <;> simp [differential] <;> ring

theorem differential_smul (r : PolynomialRing k) (v : Cube k) :
    differential (r • v) = r • differential v := by
  funext i; fin_cases i <;> simp [differential, smul_eq_mul] <;> ring

def differentialLinear (k : Type) [Field k] : Cube k →ₗ[PolynomialRing k] Cube k where
  toFun := differential
  map_add' := differential_add
  map_smul' := differential_smul

theorem differential_squared (v : Cube k) : differential (differential v) = 0 := by
  funext i; fin_cases i <;> simp [differential] <;> ring

/-- A characteristic-independent contraction; divide in the first exterior coordinate present,
then set all earlier polynomial variables to zero. -/
def contraction (v : Cube k) : Cube k := ![
  0,
  quotient 0 (v 0),
  remainder 0 (quotient 1 (v 0)),
  quotient 0 (v 2),
  remainder 0 (remainder 1 (quotient 2 (v 0))),
  quotient 0 (v 4),
  remainder 0 (quotient 1 (v 4)),
  quotient 0 (v 6),
  remainder 0 (remainder 1 (remainder 2 (quotient 3 (v 0)))),
  quotient 0 (v 8),
  remainder 0 (quotient 1 (v 8)),
  quotient 0 (v 10),
  remainder 0 (remainder 1 (quotient 2 (v 8))),
  quotient 0 (v 12),
  remainder 0 (quotient 1 (v 12)),
  quotient 0 (v 14)]

@[simp] theorem contraction_zero : contraction (0 : Cube k) = 0 := by
  funext i; fin_cases i <;> simp [contraction]

/-- Projection onto the polynomial constant-coordinate remainder at the empty mask. -/
def terminalProjection (v : Cube k) : Cube k :=
  ![remainder 0 (remainder 1 (remainder 2 (remainder 3 (v 0)))),
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem contraction_identity (v : Cube k) :
    differential (contraction v) + contraction (differential v) =
      v - terminalProjection v := by
  funext i
  fin_cases i <;>
    simp [differential, contraction, terminalProjection, remainder,
      quotient_X_mul_ne] <;> ring

end NSP3.TorSpike.Koszul
