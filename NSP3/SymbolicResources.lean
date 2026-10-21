import NSP3.SymbolicJointAxes
import NSP3.FullAccounting

namespace NSP3

/-- Disjoint existing support resources with the new joint-axis gain.
This is not the unproved BW/BF plane-defect substitution. -/
theorem fullSupport_axis_resource_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    1+max (pair12Count S.D) g.x+max (pair12Count S.D) g.y+
      max (pair12Count S.D) g.z+fullSupportAxisGain S g+
      Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      Nat.choose (pair23Count S.D) 2+(pair12ExtraFinset S).card+
      (pair13ExtraFinset S).card+(pair23ExtraFinset S).card+
      (puncturedFullCoreFinset S g).card+
      (lowerBoxFullOutsideCoreFinset S g).card ≤ S.m := by
  have hp := fullSupport_joint_axis_pressure S hg hf ho
  have ha := full_resource_accounting_lowerBox S hg hf
  have hx := pair12_intercept1_lower S
  have hy := pair12_intercept2_lower S
  have hz := pair12_return_capacity_fullSupport S hg hf
  have hxg : g.x < pure1Intercept S := (pure1_axis_mem_iff S _).mp
    (S.down_closed (b := g.pred2) ⟨le_rfl, Nat.zero_le _, Nat.zero_le _⟩
      (hg.pred2_mem hf.2.1))
  have hyg : g.y < pure2Intercept S := (pure2_axis_mem_iff S _).mp
    (S.down_closed (b := g.pred1) ⟨Nat.zero_le _, le_rfl, Nat.zero_le _⟩
      (hg.pred1_mem hf.1))
  have hzg : g.z < pure3Intercept S := (pure3_axis_mem_iff S _).mp
    (S.down_closed (b := g.pred1) ⟨Nat.zero_le _, Nat.zero_le _, le_rfl⟩
      (hg.pred1_mem hf.1))
  unfold fullM fullResourceExcess fullAxisExcess1 fullAxisExcess2 fullAxisExcess3 at ha
  omega

end NSP3
