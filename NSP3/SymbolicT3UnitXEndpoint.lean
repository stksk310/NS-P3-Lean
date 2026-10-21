import NSP3.SymbolicT3UnitXBudget
import NSP3.SymbolicT3UnitSharp

namespace NSP3

/-- Separate rank-cut and joint-axis gains sharpen BW28 to BF30. -/
theorem fullSupport_t3_unit_x_r3_BF_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=1) (hy : g.y=2) (hz : g.z=2) : 30 ≤ S.m := by
  have hs : pair13Count S.D=3 := by have := ho.1; have := ho.2; omega
  have hm := fullSupport_symbolic_BF_lower S hg hf ho
  have hH := t3_unit_x_H_card S hg hf ho ht hx (by omega) (by omega)
  have hd : ferrersPlaneDefect 3 2 2=1 := by decide
  have hp : rankCutPhi 3 2 2=2 := by
    rw [rankCutPhi_first_diagonal (by omega : 0<2) (by omega : 0<2) (by omega)]
    decide
  have hgain : fullSupportAxisGain S g=1 := by
    simp [fullSupportAxisGain,jointAxisGain,hr,hs,ht,hx,hy,hz]
  unfold fullSupportSymbolicBF fullSupportSymbolicBW at hm
  rw [hH,hgain] at hm
  simp only [hr,hs,ht,hx,hy,hz,hd,hp] at hm
  have d1 : ferrersPlaneDefect 3 1 2=2 := by decide
  have hnon : 0 ≤ max (ferrersPlaneDefect 3 1 2) (rankCutPhi 3 1 2)-
      ferrersPlaneDefect 3 1 2 := Nat.zero_le _
  norm_num [d1,Nat.choose] at hm
  omega

/-- Only the forced point list is permuted; no unproved staircase action is used. -/
theorem fullSupport_t3_unit_x_r3_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=1) (hy : g.y=2) (hz : g.z=2) : fullTarget S ≤ S.m := by
  classical
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  have hs : pair13Count S.D=3 := by have := ho.1; have := ho.2; omega
  have hb := fullSupport_t3_unit_x_r3_BF_lower S hg hf ho ht hr hx hy hz
  have htarget : fullTarget S=31 := by rw [fullTarget_eq_square,hr,hs,ht]; norm_num
  by_contra hn
  have hm : S.m=30 := by omega
  let P := t3UnitZForcedPoints.map (fun p => Point3.mk p.z p.y p.x)
  have hge : g=Point3.mk 1 2 2 := Point3.ext hx hy hz
  have hshape : ∀ p ∈ P,
      T3SmallForcedShape 3 3 3 (Point3.mk 1 2 2) p ∨ p=Point3.mk 2 1 1 := by
    dsimp [P]
    unfold T3SmallForcedShape
    decide
  have hmem : ∀ p ∈ P, p ∈ S.D := by
    intro p hp
    rcases hshape p hp with hshape | heq
    · apply t3_small_forced_shape_mem S hg hf
      simpa only [hr,hs,ht,hge] using hshape
    · subst p
      apply puncturedFullCoreFinset_subset_D S hg hf
      apply (mem_puncturedFullCoreFinset _ _ _).mpr
      constructor
      · norm_num [FullCore,hr,hs,ht]
      · intro hl
        have hh := hl.2.1
        change g.y ≤ 1 at hh
        omega
  have hd : (P.map S.residue).Nodup := List.Nodup.map_on
    (fun p hp q hq he => S.standard_eq_of_residue_eq (hmem p hp) (hmem q hq) he)
    (by decide : P.Nodup)
  have hzero := S.residue_rho g
  rw [fullSupport_return_eq_zero S hg hf,CyclicStaircase.residue_zero] at hzero
  have hh : S.p1+2*S.p2+2*S.p3=0 := by
    simpa [CyclicStaircase.residue,residueOf,hx,hy,hz] using hzero.symm
  have hrel : S.p1 = -2*S.p3-2*S.p2 := by linear_combination hh
  have hmap : (fun p : Point3 => S.residue (Point3.mk p.z p.y p.x)) =
      residueOf S.p3 S.p2 (-2*S.p3-2*S.p2) := by
    funext p
    simp only [CyclicStaircase.residue,residueOf,hrel]
    ring
  dsimp only [P] at hd
  rw [List.map_map] at hd
  change (t3UnitZForcedPoints.map (fun p => S.residue (Point3.mk p.z p.y p.x))).Nodup at hd
  rw [hmap] at hd
  let a : Fin S.m := ⟨S.p3.val,ZMod.val_lt _⟩
  let b : Fin S.m := ⟨S.p2.val,ZMod.val_lt _⟩
  have hn : (t3UnitZEndpointResidues S.m a b).Nodup := by
    simpa only [t3UnitZEndpointResidues,a,b,ZMod.natCast_zmod_val] using hd
  have hcert : ∀ a b : Fin S.m, ¬ (t3UnitZEndpointResidues S.m a b).Nodup := by
    rw [hm]
    exact t3_unit_z_endpoint_collision_30
  exact hcert a b hn

/-- Every ordered t3 minimal complement with exactly the x coordinate one. -/
theorem fullSupport_t3_one_unit_x_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    fullTarget S ≤ S.m := by
  rcases fullSupport_t3_unit_x_BW_cover S hg hf ho ht hx hy hz with hdone | ⟨hr,hs,hy',hz'⟩
  · exact hdone
  · exact fullSupport_t3_unit_x_r3_sharp S hg hf ho ht hr hx hy' hz'

end NSP3
