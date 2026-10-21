import NSP3.LargeTCofinal

namespace NSP3

#check fullSupport_large_t_strict

example :
    quarterSquareCeil (10 + 9 + 4 + 2) + Nat.choose ((9 + 4 + 2 - 10) / 2) 3 <
      3 * 10 + 1 + Nat.choose 10 2 + Nat.choose 9 2 + Nat.choose 4 2 + simplexCard 9 4 := by
  norm_num [quarterSquareCeil, simplexCard, Nat.choose]

example :
    quarterSquareCeil (11 + 7 + 7 + 2) + Nat.choose ((7 + 7 + 2 - 11) / 2) 3 <
      3 * 11 + 1 + Nat.choose 11 2 + Nat.choose 7 2 + Nat.choose 7 2 + simplexCard 7 7 := by
  norm_num [quarterSquareCeil, simplexCard, Nat.choose]

example : 7 * 5 + 3 + largeHoleCap 5 < simplexCard 7 5 := by
  norm_num [largeHoleCap, simplexCard, Nat.choose]

example : 7 * 6 + 3 + largeHoleCap 6 < simplexCard 7 6 := by
  norm_num [largeHoleCap, simplexCard, Nat.choose]

end NSP3
