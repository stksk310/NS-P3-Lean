import NSP3.SharpnessAssembly

namespace NSP3

/-- The actual presentation-cardinality supremum of all cofinite edim-four
submonoids at multiplicity m. Its literature interpretation uses m >= 4. -/
noncomputable def P3_R (m : ℕ) : ℕ := sSup (sharpRhoValues m)

end NSP3
