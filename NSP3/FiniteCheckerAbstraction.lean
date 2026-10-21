import NSP3.FiniteTerminalCheck

namespace NSP3

/-- The finite data filters applied before completion.  Every component is
computed solely from `(q,m,g,w)` and the accepted finite envelopes. -/
def EnumeratedCheckerState (q : FullResidualTuple) (m : ℕ) [NeZero m]
    (g : Point3) (w : ResidueWeights m) : Prop :=
  (q, m) ∈ strictFailureArithmeticStateFinset ∧
    g ∈ pointBox (m + 1) ∧
    w ∈ boundaryResidueWeights m g ∧
    residueInjectiveOn (mandatorySeed q g) w

instance (q : FullResidualTuple) (m : ℕ) [NeZero m]
    (g : Point3) (w : ResidueWeights m) :
    Decidable (EnumeratedCheckerState q m g w) := by
  unfold EnumeratedCheckerState
  infer_instance

/-- Complete abstraction of every actual strict ordered full-support failure
into the finite arithmetic/boundary/weight/seed state space. -/
theorem actual_strictFailure_has_enumeratedCheckerState
    (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hstrict : S.m < fullTarget S) :
    letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
    EnumeratedCheckerState
      (FullResidualTuple.mk (pair12Count S.D) (pair13Count S.D)
        (pair23Count S.D)) S.m g (actualResidueWeights S) := by
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  unfold EnumeratedCheckerState
  set_option maxRecDepth 100000 in
    exact ⟨fullSupport_strictFailure_mem_arithmeticState S hg hfull hord hstrict,
      fullSupport_minimalComplement_mem_pointBox_succ_m S hg hfull,
      actualResidueWeights_mem_boundary S hg hfull,
      actualResidueWeights_injective_on_mandatorySeed S hg hfull⟩

end NSP3
