import NSP3.FastMandatorySeed

namespace NSP3

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

example (q : FullResidualTuple) (g : Point3) :
    fastMandatorySeed q g = mandatorySeed q g := fastMandatorySeed_eq q g

example : Point3.mk 0 0 0 ∈ fastMandatorySeed ⟨0,0,0⟩ ⟨0,0,0⟩ := by decide
example : Point3.mk 0 1 1 ∈ fastMandatorySeed ⟨3,2,7⟩ ⟨1,1,1⟩ := by decide
example : Point3.mk 1 1 1 ∉ fastMandatorySeed ⟨3,3,3⟩ ⟨1,1,1⟩ := by decide
-- An unordered triple needs genuine downward closure from its yz plane.
example : Point3.mk 0 0 6 ∈ fastMandatorySeed ⟨3,2,7⟩ ⟨1,1,1⟩ := by decide

example (q : FullResidualTuple) (g : Point3) (hs : q.s ≤ q.r) (ht : q.t ≤ q.s) :
    fastMandatorySeed q g = fastRawMandatorySeed q g :=
  fastMandatorySeed_ordered_eq q g hs ht

end NSP3
