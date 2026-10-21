import NSP3.SharpnessOddWeights

namespace NSP3.Sharpness
#print axioms oddBorder_weight_injective

example (m k : ℕ) (hk : 2 ≤ k) (hm : k*k+k+1 ≤ m) :
    Set.InjOn (aperyWeight (oddA m k) (oddB m k) (oddC m k))
      (oddBorder (m-k*k-1) k) := oddBorder_weight_injective m k hk hm

example (k : ℕ) (hk : 2 ≤ k) :
    Set.InjOn (aperyWeight (oddA (k*k+k+1) k) (oddB (k*k+k+1) k)
      (oddC (k*k+k+1) k)) (oddBorder ((k*k+k+1)-k*k-1) k) :=
  oddBorder_weight_injective (k*k+k+1) k hk (by omega)

example : Set.InjOn (aperyWeight (oddA 7 2) (oddB 7 2) (oddC 7 2))
    (oddBorder (7-2*2-1) 2) := oddBorder_weight_injective 7 2 (by omega) (by omega)

example : Set.InjOn (aperyWeight (oddA 8 2) (oddB 8 2) (oddC 8 2))
    (oddBorder (8-2*2-1) 2) := oddBorder_weight_injective 8 2 (by omega) (by omega)

example : Set.InjOn (aperyWeight (oddA 13 3) (oddB 13 3) (oddC 13 3))
    (oddBorder (13-3*3-1) 3) := oddBorder_weight_injective 13 3 (by omega) (by omega)
end NSP3.Sharpness
