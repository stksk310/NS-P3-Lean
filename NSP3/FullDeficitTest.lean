import NSP3.FullDeficit

namespace NSP3

#check fullDeficitIdentity
#check fullTarget_le_fullM_add_product
#check fullDeficit_square_bound

example :
    4 * (quarterSquareCeil (0 + 0 + 0 + 2) : ℤ) +
        ((0 : ℤ) - (0 : ℤ) - (0 : ℤ) + 3) ^ 2 =
      4 * (3 * 0 + 1 + Nat.choose 0 2 + Nat.choose 0 2 + Nat.choose 0 2 : ℕ) +
        4 * (0 : ℤ) * 0 + 9 + 3 * ((0 + 0 + 0 + 2) % 2 : ℕ) :=
  fullDeficitIdentity 0 0 0

end NSP3
