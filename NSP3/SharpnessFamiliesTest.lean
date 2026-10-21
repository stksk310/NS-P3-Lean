import NSP3.SharpnessFamilies
namespace NSP3.Sharpness
example (m k : ℕ) (hk : 1 ≤ k) (hm : (k+1)^2 ≤ m) :
    MinimalFourGeneratorClass m (evenA m k) (evenB m k) (evenC m k) :=
  even_minimalFour m k hk hm
example (m k : ℕ) (hk : 2 ≤ k) (hm : k*k+k+1 ≤ m) :
    MinimalFourGeneratorClass m (oddA m k) (oddB m k) (oddC m k) :=
  odd_minimalFour m k hk hm
example : MinimalFourGeneratorClass 4 7 9 10 := even_minimalFour 4 1 (by norm_num) (by norm_num)
example : MinimalFourGeneratorClass 5 9 16 17 := even_minimalFour 5 1 (by norm_num) (by norm_num)
example : MinimalFourGeneratorClass 6 11 25 26 := even_minimalFour 6 1 (by norm_num) (by norm_num)
example : MinimalFourGeneratorClass 7 13 16 17 := odd_minimalFour 7 2 (by norm_num) (by norm_num)
example : MinimalFourGeneratorClass 8 15 26 27 := odd_minimalFour 8 2 (by norm_num) (by norm_num)
example : MinimalFourGeneratorClass 9 26 29 30 := even_minimalFour 9 2 (by norm_num) (by norm_num)
example (k : ℕ) (hk : 1 ≤ k) :
    MinimalFourGeneratorClass ((k+1)^2) (evenA ((k+1)^2) k)
      (evenB ((k+1)^2) k) (evenC ((k+1)^2) k) := even_minimalFour _ _ hk le_rfl
example (k : ℕ) (hk : 2 ≤ k) :
    MinimalFourGeneratorClass (k*k+k+1) (oddA (k*k+k+1) k)
      (oddB (k*k+k+1) k) (oddC (k*k+k+1) k) := odd_minimalFour _ _ hk le_rfl
#print axioms even_minimalFour
#print axioms odd_minimalFour
end NSP3.Sharpness
