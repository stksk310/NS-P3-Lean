import NSP3.V03
import NSP3.V03.RouteAudit

/-! Endpoint type and axiom audit, separate from the library root. -/
#check NSP3.V03.P3_MAIN
#check NSP3.V03.P4_e3
#check NSP3.V03.maximalPoints_card_add_two_le_boundary_natCard
#check NSP3.V03.pseudoFrobeniusType_upper
#check NSP3.V03.pseudoFrobeniusType_noFull_upper
#check NSP3.V03.maximumType_isGreatest
#check NSP3.V03.maximumType_window
#check NSP3.V03.presentation_type_window
#check NSP3.V03.spectrum_large_iff
#check NSP3.V03.spectrum_member_ge_three
#check NSP3.V03.spectrum_three_exists
#check NSP3.V03.multi_isolated_intrinsic_lower
#check NSP3.P3_MAIN
#check NSP3.P4_e3
#check NSP3.V03.intrinsicRho_add_m_ge_ten
#check NSP3.V03.intrinsicRho_cubic_lower
#check NSP3.V03.spectrum_three_iff
#check NSP3.V03.spectrum_four_iff
#check NSP3.V03.spectrum_five_iff
#check NSP3.V03.spectrum_all_iff
#check NSP3.V03.complete_spectrum

#print axioms NSP3.V03.P3_MAIN
#print axioms NSP3.V03.P4_e3
#print axioms NSP3.V03.maximalPoints_card_add_two_le_boundary_natCard
#print axioms NSP3.V03.pseudoFrobeniusType_upper
#print axioms NSP3.V03.pseudoFrobeniusType_noFull_upper
#print axioms NSP3.V03.maximumType_isGreatest
#print axioms NSP3.V03.maximumType_window
#print axioms NSP3.V03.presentation_type_window
#print axioms NSP3.V03.spectrum_large_iff
#print axioms NSP3.V03.spectrum_member_ge_three
#print axioms NSP3.V03.spectrum_three_exists
#print axioms NSP3.V03.multi_isolated_intrinsic_lower
#print axioms NSP3.P3_MAIN
#print axioms NSP3.P4_e3
#print axioms NSP3.V03.intrinsicRho_add_m_ge_ten
#print axioms NSP3.V03.intrinsicRho_cubic_lower
#print axioms NSP3.V03.complete_spectrum

example (m : ℕ) (hm : 4 ≤ m) : NSP3.P3_R m=NSP3.V03.T m :=
  NSP3.V03.P3_MAIN m hm

example (m : ℕ) (hm : 4 ≤ m) : NSP3.P3_R m=NSP3.C3 m ↔ m ≤ 9 :=
  NSP3.V03.P4_e3 m hm

example (m : ℕ) (hm : 4 ≤ m) :
    NSP3.V03.T m-3 ≤ NSP3.V03.maximumType m ∧
      NSP3.V03.maximumType m ≤ NSP3.V03.T m-1 :=
  NSP3.V03.maximumType_window m hm

example (m : ℕ) (hm : 4 ≤ m) :
    NSP3.sharpRhoValues m =
      if m=4 then {6} else if m=5 then {5,6} else if m=6 then {4,5,6}
      else if m=7 then {4,5,6,7} else Set.Icc 3 (NSP3.V03.T m) :=
  NSP3.V03.complete_spectrum m hm
