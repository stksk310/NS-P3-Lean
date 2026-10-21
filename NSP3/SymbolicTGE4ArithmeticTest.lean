import NSP3.SymbolicTGE4Arithmetic

namespace NSP3

-- Break caught: losing positivity or one capacity unit invalidates the product lower.
example (A B C : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) :
    A+B+C ≤ A*B*C+2 := positive_triple_product_sum_lower A B C hA hB hC

-- Break caught: any changed coefficient in the exact gap identity.
example (r s t : ℤ) :
    4*(4*r+3)+2*r*(r-1)+2*s*(s-1)+2*t*(t-1)-(r+s+t+2)^2 =
      r^2+(10-2*(s+t))*r+(s-t)^2-6*(s+t)+8 :=
  tge4_large_r_gap_identity r s t

-- Break caught: accepting insufficient budget or wrong quarter-square boundary.
example (r s t m : ℕ) (hr : 18 ≤ r) (hst : s+t ≤ 12)
    (hb : 4*r+3+Nat.choose r 2+Nat.choose s 2+Nat.choose t 2 ≤ m) :
    (r+s+t+2)^2 ≤ 4*m := tge4_large_r_square r s t m hr hst hb

-- Break caught: the stronger variable threshold must not silently require r>=18.
example (r s t m : ℕ) (hsum : 8 ≤ s+t) (hr : 2*(s+t) ≤ r+6)
    (hb : 4*r+3+Nat.choose r 2+Nat.choose s 2+Nat.choose t 2 ≤ m) :
    (r+s+t+2)^2 ≤ 4*m := tge4_variable_threshold_square r s t m hsum hr hb

end NSP3
