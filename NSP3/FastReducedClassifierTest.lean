import NSP3.FastReducedClassifier

namespace NSP3

example {m : ℕ} [NeZero m] (q : FullResidualTuple) (g : Point3)
    (w : ResidueWeights m) :
    ReducedCheckerState q m g w ↔ fastReducedState q m g w :=
  reducedState_fast_iff q g w

example {m : ℕ} [NeZero m] (q : FullResidualTuple) (g : Point3)
    (w : ResidueWeights m) (hi : residueInjectiveOn (mandatorySeed q g) w) :
    q.r < addOrderOf w.p1 := seed_injective_first_order_gt q g w hi

end NSP3
