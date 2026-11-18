import NSP3.V03.NoFullUnified
import NSP3.V03.EightProfiles

namespace NSP3.V03

#check noFull_large_arithmetic
#check noFull_unified
#check endpointH_eq_actual
#check endpointBF_eq_actual
#check eight_profiles_finite
#check eight_profiles_domain_card
#check eight_profiles_minimum_attained
#check eight_profiles_sharp

#print axioms noFull_large_arithmetic
#print axioms noFull_unified
#print axioms endpointH_eq_actual
#print axioms endpointBF_eq_actual
#print axioms eight_profiles_finite
#print axioms eight_profiles_domain_card
#print axioms eight_profiles_minimum_attained
#print axioms eight_profiles_sharp

example : endpointTarget 4 4 4=49 := by decide
example : endpointTarget 5 4 4=57 := by decide
example : endpointBF 4 4 4 1 1 4=49 := by decide
example : endpointBF 5 4 4 1 5 1=60 := by decide
example : (∑ i : Fin 8, endpointDomainCard i)=1497 := eight_profiles_total_domain

-- Non-strict ordering is deliberately accepted by the unified large range.
example (R t : ℕ) (ht : 5≤t) (htr : t≤R) :
    quarterSquareCeil (R+R+t+1) ≤ strictM5 R R t+simplexCard R t :=
  noFull_large_arithmetic R R t ht htr le_rfl

end NSP3.V03
