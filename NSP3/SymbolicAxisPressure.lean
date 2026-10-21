import Mathlib.Tactic

namespace NSP3

def jointAxisGain (h12 h13 h23 : ℕ) : ℕ :=
  max (max h12 h13) (max h23 ((h12+h13+h23+1)/2))

/-- Shared-axis arithmetic: three pairwise pressures are charged only once. -/
theorem three_axis_pressure_lower {e1 e2 e3 h12 h13 h23 : ℕ}
    (h12le : h12 ≤ e1+e2) (h13le : h13 ≤ e1+e3)
    (h23le : h23 ≤ e2+e3) : jointAxisGain h12 h13 h23 ≤ e1+e2+e3 := by
  unfold jointAxisGain
  omega

end NSP3
