import NSP3.SharpnessApery

namespace NSP3.Sharpness

#print axioms evenIndex_injective
#print axioms even_residue_injective
#print axioms odd_residue_injective
#print axioms even_weightMinimal_region
#print axioms odd_weightMinimal_region
#print axioms even_unique_factorization
#print axioms odd_unique_factorization
#print axioms even_canonical_iff
#print axioms odd_canonical_iff

example (p : Point3) : AperyCanonical 4 7 9 10 p ↔ EvenRegion 2 1 p := by
  apply even_canonical_iff 4 1 2 7 9 10 <;> norm_num

example (p : Point3) : AperyCanonical 5 9 16 17 p ↔ EvenRegion 3 1 p := by
  apply even_canonical_iff 5 1 3 9 16 17 <;> norm_num

example (p : Point3) : AperyCanonical 6 11 25 26 p ↔ EvenRegion 4 1 p := by
  apply even_canonical_iff 6 1 4 11 25 26 <;> norm_num

example (p : Point3) : AperyCanonical 7 13 16 17 p ↔ OddRegion 2 2 p := by
  apply odd_canonical_iff 7 2 2 13 16 17 <;> norm_num

example (p : Point3) : AperyCanonical 8 15 26 27 p ↔ OddRegion 3 2 p := by
  apply odd_canonical_iff 8 2 3 15 26 27 <;> norm_num

example (p : Point3) : AperyCanonical 9 26 29 30 p ↔ EvenRegion 3 2 p := by
  apply even_canonical_iff 9 2 3 26 29 30 <;> norm_num

example (p q : Point3) (hp : EvenRegion 3 2 p) (t : ℕ)
    (he : aperyWeight 26 29 30 p=t*9+aperyWeight 26 29 30 q) : t=0 ∧ q=p := by
  exact even_unique_factorization 9 2 3 26 29 30 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp t he

example (p q : Point3) (hp : OddRegion 2 2 p) (t : ℕ)
    (he : aperyWeight 13 16 17 p=t*7+aperyWeight 13 16 17 q) : t=0 ∧ q=p := by
  exact odd_unique_factorization 7 2 2 13 16 17 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hp t he

end NSP3.Sharpness
