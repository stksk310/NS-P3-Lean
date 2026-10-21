import NSP3.SymbolicAxisPressure
import NSP3.SymbolicFacePressure
import NSP3.M5Baseline
import NSP3.LowerBox

namespace NSP3

noncomputable def fullSupportAxisGain (S : CyclicStaircase) (g : Point3) : ℕ :=
  let r := pair12Count S.D
  let L1 := max r g.x
  let L2 := max r g.y
  let L3 := max r g.z
  jointAxisGain (pair12Count S.D+g.x+g.y-L1-L2)
    (pair13Count S.D+g.x+g.z-L1-L3) (pair23Count S.D+g.y+g.z-L2-L3)

/-- The complete actual-staircase joint pressure, without double-charging axes. -/
theorem fullSupport_joint_axis_pressure (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (_ho : PairCountsOrdered S) :
    fullSupportAxisGain S g ≤
      (pure1Intercept S-1-max (pair12Count S.D) g.x)+
      (pure2Intercept S-1-max (pair12Count S.D) g.y)+
      (pure3Intercept S-1-max (pair12Count S.D) g.z) := by
  have h12mem : Point3.mk g.x g.y 0 ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨le_rfl, le_rfl, Nat.zero_le _⟩,
      by intro h; have := congrArg Point3.z h; have := hf.2.2; simp_all⟩)
  have h13mem : Point3.mk g.x 0 g.z ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨le_rfl, Nat.zero_le _, le_rfl⟩,
      by intro h; have := congrArg Point3.y h; have := hf.2.1; simp_all⟩)
  have h23mem : Point3.mk 0 g.y g.z ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨Nat.zero_le _, le_rfl, le_rfl⟩,
      by intro h; have := congrArg Point3.x h; have := hf.1; simp_all⟩)
  have h12 := pair12_face_axis_pressure S h12mem
  have h13 := pair13_face_axis_pressure S h13mem
  have h23 := pair23_face_axis_pressure S h23mem
  have hxmem : Point3.mk g.x 0 0 ∈ S.D := S.down_closed
    (b := Point3.mk g.x g.y 0) ⟨le_rfl, Nat.zero_le _, le_rfl⟩ h12mem
  have hymem : Point3.mk 0 g.y 0 ∈ S.D := S.down_closed
    (b := Point3.mk g.x g.y 0) ⟨Nat.zero_le _, le_rfl, le_rfl⟩ h12mem
  have hzmem : Point3.mk 0 0 g.z ∈ S.D := S.down_closed
    (b := Point3.mk g.x 0 g.z) ⟨Nat.zero_le _, le_rfl, le_rfl⟩ h13mem
  have hx := (pure1_axis_mem_iff S _).mp hxmem
  have hy := (pure2_axis_mem_iff S _).mp hymem
  have hz := (pure3_axis_mem_iff S _).mp hzmem
  have hrx := pair12_intercept1_lower S
  have hry := pair12_intercept2_lower S
  have hrz := pair12_return_capacity_fullSupport S hg hf
  unfold fullSupportAxisGain
  apply three_axis_pressure_lower <;> omega

end NSP3
