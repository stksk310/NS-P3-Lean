import NSP3.V03.SpectrumFourLower

namespace NSP3.V03

/-- Four relations are attained by an actual semigroup at every multiplicity at least six. -/
theorem spectrum_four_exists (m : ℕ) (hm : 6 ≤ m) : 4∈sharpRhoValues m := by
  have hclass := four_family_minimalFour345 m hm
  have hrho : intrinsicRho (generatedSemigroup m (3*(m+1)) (4*(m+1))
      (5*(m+1)))=4 :=
    le_antisymm (rho_four345_le_four m hm) (rho_four345_ge_four_all m hm)
  have hs := minimal_generator_class_bridge _ _ _ _ hclass
  exact ⟨generatedAddSubmonoid m (3*(m+1)) (4*(m+1)) (5*(m+1)),
    hs.2.2.2,hs.2.2.1,hs.1,hrho⟩

end NSP3.V03
