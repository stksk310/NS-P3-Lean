import NSP3.FastReducedClassifier

namespace NSP3
example (m : ℕ) [NeZero m] : fastDivisorResidueWeights m = divisorResidueWeights m :=
  fastDivisorResidueWeights_eq m
end NSP3
