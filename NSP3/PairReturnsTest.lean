import NSP3.PairReturns

namespace NSP3

open CyclicStaircase

example (S : CyclicStaircase) {b : Point3} (hb : MinimalComplement S.D b)
    (hp : Pair12 b) : ∃ c : ℕ, S.rho b = ⟨0, 0, c⟩ :=
  pair12_return_eq_axis3 S hb hp

example (S : CyclicStaircase) {b : Point3} (hb : MinimalComplement S.D b)
    (hp : Pair13 b) : ∃ c : ℕ, S.rho b = ⟨0, c, 0⟩ :=
  pair13_return_eq_axis2 S hb hp

example (S : CyclicStaircase) {b : Point3} (hb : MinimalComplement S.D b)
    (hp : Pair23 b) : ∃ c : ℕ, S.rho b = ⟨c, 0, 0⟩ :=
  pair23_return_eq_axis1 S hb hp

example (S : CyclicStaircase) : Function.Injective (pair12ReturnCoord S) :=
  pair12ReturnCoord_injective S

example (S : CyclicStaircase) : Function.Injective (pair13ReturnCoord S) :=
  pair13ReturnCoord_injective S

example (S : CyclicStaircase) : Function.Injective (pair23ReturnCoord S) :=
  pair23ReturnCoord_injective S

end NSP3
