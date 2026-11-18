import NSP3.V03.SpectrumFourLower

namespace NSP3.V03
open NSP3.CommonCard

#check glued_small_unique
#check pureMultiplicity_isolated
#check four345Vector_isolated
#check four345_witnesses
#check rho_four345_ge_four_all

#print axioms glued_small_unique
#print axioms pureMultiplicity_isolated
#print axioms rho_four345_ge_four_all

-- These are exactly the collisions that a distinct-degree lower bound misses.
example : degree ![8,27,36,45] (four345Vector 8 0)=
    degree ![8,27,36,45] (four345Vector 8 3) := by decide
example : degree ![9,30,40,50] (four345Vector 9 1)=
    degree ![9,30,40,50] (four345Vector 9 3) := by decide
example : degree ![10,33,44,55] (four345Vector 10 2)=
    degree ![10,33,44,55] (four345Vector 10 3) := by decide

example : four345Vector 8 0≠four345Vector 8 3 := by decide
example : 4 ≤ intrinsicRho (generatedSemigroup 8 27 36 45) :=
  rho_four345_ge_four_all 8 (by decide)
example : 4 ≤ intrinsicRho (generatedSemigroup 9 30 40 50) :=
  rho_four345_ge_four_all 9 (by decide)
example : 4 ≤ intrinsicRho (generatedSemigroup 10 33 44 55) :=
  rho_four345_ge_four_all 10 (by decide)

end NSP3.V03
