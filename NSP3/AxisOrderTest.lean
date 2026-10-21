import NSP3.AxisOrder

namespace NSP3

#check axis1_addOrder_lower
#check axis2_addOrder_lower
#check axis3_addOrder_lower

example (S : CyclicStaircase) :
    pure1Intercept S ≤ addOrderOf S.p1 := axis1_addOrder_lower S

end NSP3
