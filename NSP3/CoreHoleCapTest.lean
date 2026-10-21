import NSP3.CoreHoleCap

namespace NSP3

#check coreHoleHeight
#check largeHoleCap
#check coreHole_card_le_choose_height
#check coreHole_card_le_largeHoleCap

example : largeHoleCap 4 = 1 := by norm_num [largeHoleCap, Nat.choose]
example : largeHoleCap 5 = 1 := by norm_num [largeHoleCap, Nat.choose]
example : largeHoleCap 6 = 4 := by norm_num [largeHoleCap, Nat.choose]

end NSP3
