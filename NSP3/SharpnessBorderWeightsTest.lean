import NSP3.SharpnessBorderWeights

namespace NSP3.Sharpness
example (m k : ℕ) (hk : 1 ≤ k) (hm : (k+1)^2 ≤ m) :
    ∀ p ∈ evenBorder (m-k*k-k) k, ∃ t q, 0 < t ∧
      aperyWeight (evenA m k) (evenB m k) (evenC m k) p =
        t*m+aperyWeight (evenA m k) (evenB m k) (evenC m k) q :=
  evenBorder_reduction m k hk hm
example (m k : ℕ) (hk : 2 ≤ k) (hm : k*k+k+1 ≤ m) :
    ∀ p ∈ oddBorder (m-k*k-1) k, ∃ t q, 0 < t ∧
      aperyWeight (oddA m k) (oddB m k) (oddC m k) p =
        t*m+aperyWeight (oddA m k) (oddB m k) (oddC m k) q :=
  oddBorder_reduction m k hk hm
example (m k : ℕ) (hk : 1 ≤ k) (hm : (k+1)^2 ≤ m) :
    Set.InjOn (aperyWeight (evenA m k) (evenB m k) (evenC m k))
      (evenBorder (m-k*k-k) k : Set Point3) := evenBorder_weight_injective m k hk hm
example : Set.InjOn (aperyWeight (evenA 4 1) (evenB 4 1) (evenC 4 1))
    (evenBorder (4-1*1-1) 1 : Set Point3) := evenBorder_weight_injective 4 1 (by norm_num) (by norm_num)
example : Set.InjOn (aperyWeight (evenA 9 2) (evenB 9 2) (evenC 9 2))
    (evenBorder (9-2*2-2) 2 : Set Point3) := evenBorder_weight_injective 9 2 (by norm_num) (by norm_num)
#print axioms evenBorder_weight_injective
#print axioms evenBorder_reduction
#print axioms oddBorder_reduction
end NSP3.Sharpness


