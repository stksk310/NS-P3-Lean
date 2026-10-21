import NSP3.SymbolicBWRows

namespace NSP3

example (r r' s t : ℕ) (h : r ≤ r') :
    coreCardRows r s t ≤ coreCardRows r' s t :=
  coreCardRows_mono_first r r' s t h

example (r s : ℕ) (hs : 4 ≤ s) (hr : s ≤ r) :
    6*s = coreCardRows r s 4+
      (if r=s then 13 else if r=s+1 then 11 else 10) :=
  coreCardRows_t4_card r s hs hr

example (r s : ℕ) (hs : 5 ≤ s) (hr : s ≤ r) :
    10*s ≤ coreCardRows r s 5+27 :=
  coreCardRows_t5_lower r s hs hr

example (r s : ℕ) (hs : 5 ≤ s) (hr : s+1 ≤ r) :
    10*s ≤ coreCardRows r s 5+23 :=
  coreCardRows_t5_strict_lower r s hs hr

example (r s : ℕ) (hs : 6 ≤ s) (hr : s ≤ r) :
    15*s ≤ coreCardRows r s 6+48 :=
  coreCardRows_t6_lower r s hs hr

end NSP3
