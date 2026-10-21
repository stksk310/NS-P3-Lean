import NSP3.SymbolicBWPressure

namespace NSP3

example (r A B : ℕ) (h : A+B ≤ r) : A*B ≤ ferrersW r A B := by
  exact ferrersW_endpoint_lower r A B h

example (r A B : ℕ) (h : A+B ≤ r) :
    (r-B+1-A)*(A*B) ≤ ferrersW r A B := by
  exact ferrersW_interval_product_lower r A B h

example (r A B : ℕ) (hr : 1 ≤ r) (ha : 1 ≤ A) (hb : 1 ≤ B) :
    A+B-r ≤ (ferrersRectangle r A B).card := by
  exact ferrersRectangle_diagonal_lower r A B hr ha hb

example (r A B : ℕ) (hr : 1 ≤ r) (ha : 1 ≤ A) (hb : 1 ≤ B) :
    max 1 (if A+B ≤ r then (r-B+1-A)*(A*B) else A+B-r) ≤
      ferrersPlaneDefect r A B := by
  exact ferrersPlaneDefect_pressure_lower r A B hr ha hb

end NSP3
