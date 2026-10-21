import NSP3.SymbolicFerrersAlgebra
namespace NSP3.Ferrers
-- The exact expansion, including cross terms, must be universal in the sequences.
example (n : ℕ) (u v : ℕ → ℕ) :
    upperSum n (fun i j => (1+u i)*(1+v j)) =
      Nat.choose n 2+n+
      (Finset.range n).sum (fun i => (n-i)*u i)+
      (Finset.range n).sum (fun j => (j+1)*v j)+upperSum n (fun i j => u i*v j) :=
  upperSum_expand n u v
end NSP3.Ferrers
