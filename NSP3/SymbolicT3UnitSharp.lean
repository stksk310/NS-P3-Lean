import NSP3.SymbolicT3UnitEndpoint
import NSP3.SymbolicT3UnitCertificate
import NSP3.SymbolicT3NonunitSharp

namespace NSP3

/-- Geometric membership of every point used in the sole congruence endpoint. -/
theorem t3_unit_z_forced_points_mem (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (hr : pair12Count S.D=3) (hs : pair13Count S.D=3) (ht : pair23Count S.D=3)
    (hx : g.x=2) (hy : g.y=2) (hz : g.z=1) :
    ∀ p ∈ t3UnitZForcedPoints, p ∈ S.D := by
  have hge : g=Point3.mk 2 2 1 := Point3.ext hx hy hz
  have shape : ∀ p ∈ t3UnitZForcedPoints,
      T3SmallForcedShape 3 3 3 (Point3.mk 2 2 1) p ∨ p=Point3.mk 1 1 2 := by
    unfold T3SmallForcedShape
    decide
  intro p hp
  rcases shape p hp with hshape | heq
  · apply t3_small_forced_shape_mem S hg hf
    simpa only [hr,hs,ht,hge] using hshape
  · subst p
    apply puncturedFullCoreFinset_subset_D S hg hf
    apply (mem_puncturedFullCoreFinset _ _ _).mpr
    constructor
    · norm_num [FullCore,hr,hs,ht]
    · intro hl
      have := hl.1
      simp only [hx,Point3.mk.injEq] at this
      omega

/-- Derived from the actual full-support terminal return, not an assumed congruence. -/
theorem t3_unit_z_weight_relation (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (hx : g.x=2) (hy : g.y=2) (hz : g.z=1) : S.p3 = -2*S.p1-2*S.p2 := by
  have h := S.residue_rho g
  rw [fullSupport_return_eq_zero S hg hf,CyclicStaircase.residue_zero] at h
  have hh : 2*S.p1+2*S.p2+S.p3=0 := by
    simpa [CyclicStaircase.residue,residueOf,hx,hy,hz] using h.symm
  linear_combination hh

/-- q333/g221: BF forces m≥30; at m=30 the return forces a standard-point collision. -/
theorem fullSupport_t3_unit_z_r3_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=2) (hy : g.y=2) (hz : g.z=1) : fullTarget S ≤ S.m := by
  classical
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  have hs : pair13Count S.D=3 := by have := ho.1;have := ho.2;omega
  have hb := fullSupport_t3_unit_z_r3_BF_lower S hg hf ho ht hr hx hy hz
  have htarget : fullTarget S=31 := by rw [fullTarget_eq_square,hr,hs,ht];norm_num
  by_contra hn
  have hm : S.m=30 := by omega
  have hmem := t3_unit_z_forced_points_mem S hg hf hr hs ht hx hy hz
  have hd : (t3UnitZForcedPoints.map S.residue).Nodup :=
    List.Nodup.map_on (fun p hp q hq he =>
      S.standard_eq_of_residue_eq (hmem p hp) (hmem q hq) he)
      (by decide : t3UnitZForcedPoints.Nodup)
  have hrel := t3_unit_z_weight_relation S hg hf hx hy hz
  let a : Fin S.m := ⟨S.p1.val,ZMod.val_lt _⟩
  let b : Fin S.m := ⟨S.p2.val,ZMod.val_lt _⟩
  have hn : (t3UnitZEndpointResidues S.m a b).Nodup := by
    change (t3UnitZForcedPoints.map (residueOf S.p1 S.p2 S.p3)).Nodup at hd
    simpa only [t3UnitZEndpointResidues,a,b,ZMod.natCast_zmod_val,←hrel] using hd
  have hcert : ∀ a b : Fin S.m, ¬ (t3UnitZEndpointResidues S.m a b).Nodup := by
    rw [hm]
    exact t3_unit_z_endpoint_collision_30
  exact hcert a b hn

/-- All ordered t3 configurations with precisely the z coordinate equal to one. -/
theorem fullSupport_t3_one_unit_z_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hz : g.z=1) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) :
    fullTarget S ≤ S.m := by
  obtain hdone | h433 | hbal | h443 :=
    fullSupport_t3_unit_z_symbolic_cover S hg hf ho ht hz hx hy
  · exact hdone
  · exact fullSupport_t3_unit_z_small_BF_sharp S hg hf ho ht hz (Or.inl h433)
  · obtain ⟨heq,hr5,hx',hy'⟩ := hbal
    have hr3 : 3 ≤ pair12Count S.D := by have := ho.1;have := ho.2;omega
    have cases : pair12Count S.D=3 ∨ pair12Count S.D=4 ∨ pair12Count S.D=5 := by omega
    rcases cases with hr | hr | hr
    · exact fullSupport_t3_unit_z_r3_sharp S hg hf ho ht hr (by omega) hy' hz
    · exact fullSupport_t3_unit_z_small_BF_sharp S hg hf ho ht hz
        (Or.inr (Or.inl ⟨hr,by omega,by omega,hy'⟩))
    · exact fullSupport_t3_unit_z_small_BF_sharp S hg hf ho ht hz
        (Or.inr (Or.inr (Or.inl ⟨hr,by omega,by omega,hy'⟩)))
  · exact fullSupport_t3_unit_z_small_BF_sharp S hg hf ho ht hz
      (Or.inr (Or.inr (Or.inr h443)))

end NSP3
