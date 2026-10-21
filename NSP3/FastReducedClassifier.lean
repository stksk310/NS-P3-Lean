import NSP3.FiniteNormalizedState
import NSP3.FastDivisorWeights
import NSP3.FastMandatorySeed

namespace NSP3

set_option maxRecDepth 100000

/-- Exact first-divisor-normalized weight filter. No stabilizer quotient and no
unit-coefficient assumption. The boundary equation retains every p3 lift. -/
def fastReducedWeightCandidates (q : FullResidualTuple) (m : ℕ) [NeZero m]
    (g : Point3) : Finset (ResidueWeights m) :=
  (fastDivisorResidueWeights m).filter fun w =>
    residueWithWeights w g = 0 ∧ residueInjectiveOn (fastMandatorySeed q g) w

def fastSeedFeasible (q : FullResidualTuple) (m : ℕ) (g : Point3) : Prop :=
  FullSupport g ∧ (fastMandatorySeed q g).card ≤ m ∧
    g ∉ fastMandatorySeed q g ∧ (g.x+1)*(g.y+1)*(g.z+1)-1 ≤ m

instance (q : FullResidualTuple) (m : ℕ) (g : Point3) :
    Decidable (fastSeedFeasible q m g) := by
  unfold fastSeedFeasible
  infer_instance

def fastReducedState (q : FullResidualTuple) (m : ℕ) [NeZero m]
    (g : Point3) (w : ResidueWeights m) : Prop :=
  (q,m) ∈ strictFailureArithmeticStateFinset ∧ g ∈ pointBox (m+1) ∧
    fastSeedFeasible q m g ∧ w ∈ fastReducedWeightCandidates q m g

instance (q : FullResidualTuple) (m : ℕ) [NeZero m] (g : Point3)
    (w : ResidueWeights m) : Decidable (fastReducedState q m g w) := by
  unfold fastReducedState
  infer_instance

theorem reducedState_fast_iff {m : ℕ} [NeZero m] (q : FullResidualTuple)
    (g : Point3) (w : ResidueWeights m) :
    ReducedCheckerState q m g w ↔ fastReducedState q m g w := by
  simp only [ReducedCheckerState,EnumeratedCheckerState,mem_boundaryResidueWeights,
    SeedFeasible,fastReducedState,fastSeedFeasible,fastReducedWeightCandidates,
    Finset.mem_filter,fastMandatorySeed_eq,fastDivisorResidueWeights_eq]
  tauto

/-- Forced x-axis points make its additive order strictly larger than q.r.
This is valid for nonunit coefficients, unlike a p1=1 shortcut. -/
theorem seed_injective_first_order_gt {m : ℕ} [NeZero m]
    (q : FullResidualTuple) (g : Point3) (w : ResidueWeights m)
    (hi : residueInjectiveOn (mandatorySeed q g) w) : q.r < addOrderOf w.p1 := by
  by_contra h
  have hn : addOrderOf w.p1 ≤ q.r := Nat.le_of_not_gt h
  have hp : Point3.mk (addOrderOf w.p1) 0 0 ∈ mandatorySeed q g := by
    rw [mem_mandatorySeed]
    refine ⟨_,(mem_rawMandatorySeed q g _).mpr ?_,le_rfl⟩
    exact Or.inr (Or.inl ⟨rfl,rfl,hn⟩)
  have hz : Point3.zero ∈ mandatorySeed q g := by
    rw [mem_mandatorySeed]
    refine ⟨_,(mem_rawMandatorySeed q g _).mpr ?_,le_rfl⟩
    exact Or.inr (Or.inl ⟨rfl,rfl,Nat.zero_le _⟩)
  have he : residueWithWeights w ⟨addOrderOf w.p1,0,0⟩ =
      residueWithWeights w Point3.zero := by
    simp only [residueWithWeights,residueOf,Point3.zero, Nat.cast_zero,
      zero_mul,add_zero]
    simpa only [nsmul_eq_mul] using (addOrderOf_nsmul_eq_zero w.p1)
  have heq := (Finset.card_image_iff.mp hi) hp hz he
  have hc := congrArg Point3.x heq
  have hpos := addOrderOf_pos w.p1
  change addOrderOf w.p1 = 0 at hc
  omega

end NSP3
