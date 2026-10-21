import NSP3.ModularIntercepts

namespace NSP3

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    S.rho g = Point3.zero :=
  fullSupport_return_eq_zero S hg hfull

example (S : CyclicStaircase) {g b : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hb : MinimalComplement S.D b) (hp : Pair12 b) :
    S.rho b ≠ Point3.zero :=
  pair12_return_ne_zero_of_fullSupport S hg hfull hb hp

example (S : CyclicStaircase) : pair12Count S.D ≤ pure3Intercept S :=
  pair12_return_capacity S

example (S : CyclicStaircase) : pair13Count S.D ≤ pure2Intercept S :=
  pair13_return_capacity S

example (S : CyclicStaircase) : pair23Count S.D ≤ pure1Intercept S :=
  pair23_return_capacity S

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    pair12Count S.D + 1 ≤ pure3Intercept S :=
  pair12_return_capacity_fullSupport S hg hfull

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    pair13Count S.D + 1 ≤ pure2Intercept S :=
  pair13_return_capacity_fullSupport S hg hfull

example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    pair23Count S.D + 1 ≤ pure1Intercept S :=
  pair23_return_capacity_fullSupport S hg hfull

example (S : CyclicStaircase) : pair12Count S.D + 1 ≤ pure1Intercept S :=
  pair12_intercept1_lower S

example (S : CyclicStaircase) : pair12Count S.D + 1 ≤ pure2Intercept S :=
  pair12_intercept2_lower S

example (S : CyclicStaircase) : pair13Count S.D + 1 ≤ pure1Intercept S :=
  pair13_intercept1_lower S

example (S : CyclicStaircase) : pair13Count S.D + 1 ≤ pure3Intercept S :=
  pair13_intercept3_lower S

example (S : CyclicStaircase) : pair23Count S.D + 1 ≤ pure2Intercept S :=
  pair23_intercept2_lower S

example (S : CyclicStaircase) : pair23Count S.D + 1 ≤ pure3Intercept S :=
  pair23_intercept3_lower S

example (S : CyclicStaircase) (hq : pair12Count S.D = 0) :
    pair12Count S.D ≤ pure3Intercept S := by
  omega

end NSP3
