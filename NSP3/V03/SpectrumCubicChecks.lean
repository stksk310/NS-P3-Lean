import NSP3.V03.SpectrumCubicLower

namespace NSP3.V03
open NSP3.CommonCard NSP3.Sharpness

#check cubicSpace_finrank
#check raw_context_mem
#check generated_cubic_mem
#check cubicGenerators_span_top
#check numericPresentation_cubic_lower
#check intrinsicRho_cubic_lower
#check rho_three_multiplicity_ge_eight

#print axioms generated_cubic_mem
#print axioms cubicGenerators_span_top
#print axioms intrinsicRho_cubic_lower
#print axioms rho_three_multiplicity_ge_eight

-- Degree three survives, while degree four and positive m-coefficients vanish.
example : cubicProj ![0,3,0,0]
    ⟨⟨3,0,0⟩,(mem_cubicPoints _).mpr (by decide)⟩=1 := by decide
example : cubicProj ![0,4,0,0]=0 := cubicProj_zero_high (by decide)
example : cubicProj ![1,0,0,0]=0 := cubicProj_zero_m (by decide)

-- The missing multiplicity-seven case is an unconditional actual-class consequence.
example (a b c : ℕ) (h : MinimalFourGeneratorClass 7 a b c) :
    intrinsicRho (generatedSemigroup 7 a b c)≠3 := by
  intro he
  have hm := rho_three_multiplicity_ge_eight 7 a b c h he
  omega

example (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) (hm : m ≤ 7) :
    4 ≤ intrinsicRho (generatedSemigroup m a b c) := by
  have hl := intrinsicRho_cubic_lower m a b c h
  omega

end NSP3.V03
