import NSP3.SymbolicT3UnitYCover
import NSP3.SymbolicT3UnitSharp

namespace NSP3

/-- q333/g212 uses actual forced points and the frozen single-modulus certificate.
Only a finite list of points is relabelled; no staircase permutation is assumed. -/
theorem fullSupport_t3_unit_y_r3_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=2) (hy : g.y=1) (hz : g.z=2) : fullTarget S ≤ S.m := by
  classical
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  have hs : pair13Count S.D=3 := by have := ho.1;have := ho.2;omega
  have hb := fullSupport_t3_unit_y_r3_BF_lower S hg hf ho ht hr hx hy hz
  have htarget : fullTarget S=31 := by rw [fullTarget_eq_square,hr,hs,ht];norm_num
  by_contra hn
  have hm : S.m=30 := by omega
  let P := t3UnitZForcedPoints.map (fun p => Point3.mk p.x p.z p.y)
  have hge : g=Point3.mk 2 1 2 := Point3.ext hx hy hz
  have hshape : ∀ p ∈ P,
      T3SmallForcedShape 3 3 3 (Point3.mk 2 1 2) p ∨ p=Point3.mk 1 2 1 := by
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
        have hh := hl.1
        change g.x ≤ 1 at hh
        omega
  have hd : (P.map S.residue).Nodup := List.Nodup.map_on
    (fun p hp q hq he => S.standard_eq_of_residue_eq (hmem p hp) (hmem q hq) he)
    (by decide : P.Nodup)
  have hzero := S.residue_rho g
  rw [fullSupport_return_eq_zero S hg hf,CyclicStaircase.residue_zero] at hzero
  have hh : 2*S.p1+S.p2+2*S.p3=0 := by
    simpa [CyclicStaircase.residue,residueOf,hx,hy,hz] using hzero.symm
  have hrel : S.p2 = -2*S.p1-2*S.p3 := by linear_combination hh
  have hmap : (fun p : Point3 => S.residue (Point3.mk p.x p.z p.y)) =
      residueOf S.p1 S.p3 (-2*S.p1-2*S.p3) := by
    funext p
    simp only [CyclicStaircase.residue,residueOf,hrel]
    ring
  dsimp only [P] at hd
  rw [List.map_map] at hd
  change (t3UnitZForcedPoints.map (fun p => S.residue (Point3.mk p.x p.z p.y))).Nodup at hd
  rw [hmap] at hd
  let a : Fin S.m := ⟨S.p1.val,ZMod.val_lt _⟩
  let b : Fin S.m := ⟨S.p3.val,ZMod.val_lt _⟩
  have hn : (t3UnitZEndpointResidues S.m a b).Nodup := by
    simpa only [t3UnitZEndpointResidues,a,b,ZMod.natCast_zmod_val] using hd
  have hcert : ∀ a b : Fin S.m, ¬ (t3UnitZEndpointResidues S.m a b).Nodup := by
    rw [hm]
    exact t3_unit_z_endpoint_collision_30
  exact hcert a b hn

/-- Every actual ordered t3 minimal complement with exactly the y coordinate one. -/
theorem fullSupport_t3_one_unit_y_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z) :
    fullTarget S ≤ S.m := by
  by_cases he : pair12Count S.D=pair13Count S.D
  · rcases fullSupport_t3_unit_y_balanced_cover S hg hf ho ht hy hx hz he with hdone | hsmall | h4
    · exact hdone
    · obtain ⟨hr5,hx',hz'⟩ := hsmall
      have hr3 : 3 ≤ pair12Count S.D := by have := ho.1;omega
      have hc : pair12Count S.D=3 ∨ pair12Count S.D=4 ∨ pair12Count S.D=5 := by omega
      rcases hc with hr | hr | hr
      · exact fullSupport_t3_unit_y_r3_sharp S hg hf ho ht hr (by omega) hy hz'
      · exact fullSupport_t3_unit_y_small_BF_sharp S hg hf ho ht hy
          (Or.inl ⟨hr,by omega,by omega,hz'⟩)
      · exact fullSupport_t3_unit_y_small_BF_sharp S hg hf ho ht hy
          (Or.inr (Or.inl ⟨hr,by omega,by omega,hz'⟩))
    · obtain ⟨hr,hx',hz'⟩ := h4
      exact fullSupport_t3_unit_y_small_BF_sharp S hg hf ho ht hy
        (Or.inr (Or.inr ⟨hr,by omega,hx',hz'⟩))
  · exact fullSupport_t3_unit_y_nonbalanced_sharp S hg hf ho ht hy hx hz (by have := ho.2;omega)

end NSP3
