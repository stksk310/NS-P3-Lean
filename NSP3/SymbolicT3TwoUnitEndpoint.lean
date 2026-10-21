import NSP3.SymbolicT3TwoUnitArithmetic
import NSP3.SymbolicT3NonunitSharp
import NSP3.SymbolicT3R3Certificate

namespace NSP3

/-- Only a finite forced point list is transported, not the staircase. -/
theorem t3_two_unit_131_points_mem (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (h12 : pair12Count S.D=3) (h13 : pair13Count S.D=3) (h23 : pair23Count S.D=3)
    (hx : g.x=1) (hy : g.y=3) (hz : g.z=1) :
    ∀ p ∈ t3r3ForcedPoints, Point3.mk p.y p.x p.z ∈ S.D := by
  have hge : g=Point3.mk 1 3 1 := Point3.ext hx hy hz
  let P := t3r3ForcedPoints.map (fun p => Point3.mk p.y p.x p.z)
  have hshape : ∀ p ∈ P, T3SmallForcedShape 3 3 3 (Point3.mk 1 3 1) p ∨
      ((0<p.x ∧ 0<p.y ∧ 0<p.z ∧ p.x+p.y≤3 ∧ p.x+p.z≤3 ∧ p.y+p.z≤3) ∧
        ¬ (1 ≤ p.x ∧ 3 ≤ p.y ∧ 1 ≤ p.z)) := by
    dsimp [P]
    unfold T3SmallForcedShape
    decide
  intro p hp
  have hm : Point3.mk p.y p.x p.z ∈ P := List.mem_map.mpr ⟨p,hp,rfl⟩
  rcases hshape _ hm with hs | hc
  · apply t3_small_forced_shape_mem S hg hf
    simpa only [h12,h13,h23,hge] using hs
  · apply puncturedFullCoreFinset_subset_D S hg hf
    apply (mem_puncturedFullCoreFinset _ _ _).mpr
    exact ⟨by simpa only [FullCore,h12,h13,h23] using hc.1,
      by rw [hge]; exact hc.2⟩

/-- BW fixes m>=27; actual zero return supplies the transported collision relation. -/
theorem t3_two_unit_131_no_go (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=1) (hy : g.y=3) (hz : g.z=1)
    (hm : S.m ≤ 30) : False := by
  classical
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  have hs : pair13Count S.D=3 := by have:=ho.1;have:=ho.2;omega
  have he := t3_two_unit_1h1_BW_exact S hg hf ho ht hx hz
  have hb := fullSupport_symbolic_BW_lower S hg hf ho
  have hlo : 27 ≤ S.m := by
    have hw : ferrersW 3 1 1=2 := by decide
    simp only [hr,hs,hy,hz,hw] at he
    norm_num [Nat.choose] at he
    omega
  let P := t3r3ForcedPoints.map (fun p => Point3.mk p.y p.x p.z)
  have hmem : ∀ p ∈ P,p ∈ S.D := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q,hq,rfl⟩
    exact t3_two_unit_131_points_mem S hg hf hr hs ht hx hy hz q hq
  have hd : (P.map S.residue).Nodup := List.Nodup.map_on
    (fun p hp q hq he => S.standard_eq_of_residue_eq (hmem p hp) (hmem q hq) he)
    (by decide : P.Nodup)
  have hzero := S.residue_rho g
  rw [fullSupport_return_eq_zero S hg hf,CyclicStaircase.residue_zero] at hzero
  have hh : S.p1+3*S.p2+S.p3=0 := by
    simpa [CyclicStaircase.residue,residueOf,hx,hy,hz] using hzero.symm
  have hrel : S.p3 = -3*S.p2-S.p1 := by linear_combination hh
  have hmap : (fun p : Point3 => S.residue (Point3.mk p.y p.x p.z)) =
      residueOf S.p2 S.p1 (-3*S.p2-S.p1) := by
    funext p
    simp only [CyclicStaircase.residue,residueOf,hrel]
    ring
  dsimp only [P] at hd
  rw [List.map_map] at hd
  change (t3r3ForcedPoints.map (fun p => S.residue (Point3.mk p.y p.x p.z))).Nodup at hd
  rw [hmap] at hd
  let a : Fin S.m := ⟨S.p2.val,ZMod.val_lt _⟩
  let b : Fin S.m := ⟨S.p1.val,ZMod.val_lt _⟩
  have hn : (t3r3EndpointResidues S.m a b).Nodup := by
    simpa only [t3r3EndpointResidues,a,b,ZMod.natCast_zmod_val] using hd
  exact t3r3_endpoint_residue_collision S.m hlo hm a b hn

/-- Only a finite forced point list is transported, not the staircase. -/
theorem t3_two_unit_113_points_mem (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (h12 : pair12Count S.D=3) (h13 : pair13Count S.D=3) (h23 : pair23Count S.D=3)
    (hx : g.x=1) (hy : g.y=1) (hz : g.z=3) :
    ∀ p ∈ t3r3ForcedPoints, Point3.mk p.z p.y p.x ∈ S.D := by
  have hge : g=Point3.mk 1 1 3 := Point3.ext hx hy hz
  let P := t3r3ForcedPoints.map (fun p => Point3.mk p.z p.y p.x)
  have hshape : ∀ p ∈ P, T3SmallForcedShape 3 3 3 (Point3.mk 1 1 3) p ∨
      ((0<p.x ∧ 0<p.y ∧ 0<p.z ∧ p.x+p.y≤3 ∧ p.x+p.z≤3 ∧ p.y+p.z≤3) ∧
        ¬ (1 ≤ p.x ∧ 1 ≤ p.y ∧ 3 ≤ p.z)) := by
    dsimp [P]
    unfold T3SmallForcedShape
    decide
  intro p hp
  have hm : Point3.mk p.z p.y p.x ∈ P := List.mem_map.mpr ⟨p,hp,rfl⟩
  rcases hshape _ hm with hs | hc
  · apply t3_small_forced_shape_mem S hg hf
    simpa only [h12,h13,h23,hge] using hs
  · apply puncturedFullCoreFinset_subset_D S hg hf
    apply (mem_puncturedFullCoreFinset _ _ _).mpr
    exact ⟨by simpa only [FullCore,h12,h13,h23] using hc.1,
      by rw [hge]; exact hc.2⟩

/-- BW fixes m>=27; actual zero return supplies the transported collision relation. -/
theorem t3_two_unit_113_no_go (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=1) (hy : g.y=1) (hz : g.z=3)
    (hm : S.m ≤ 30) : False := by
  classical
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  have hs : pair13Count S.D=3 := by have:=ho.1;have:=ho.2;omega
  have he := t3_two_unit_11h_BW_exact S hg hf ho ht hx hy
  have hb := fullSupport_symbolic_BW_lower S hg hf ho
  have hlo : 27 ≤ S.m := by
    have hw : ferrersW 3 1 1=2 := by decide
    simp only [hr,hs,hy,hz,hw] at he
    norm_num [Nat.choose] at he
    omega
  let P := t3r3ForcedPoints.map (fun p => Point3.mk p.z p.y p.x)
  have hmem : ∀ p ∈ P,p ∈ S.D := by
    intro p hp
    rcases List.mem_map.mp hp with ⟨q,hq,rfl⟩
    exact t3_two_unit_113_points_mem S hg hf hr hs ht hx hy hz q hq
  have hd : (P.map S.residue).Nodup := List.Nodup.map_on
    (fun p hp q hq he => S.standard_eq_of_residue_eq (hmem p hp) (hmem q hq) he)
    (by decide : P.Nodup)
  have hzero := S.residue_rho g
  rw [fullSupport_return_eq_zero S hg hf,CyclicStaircase.residue_zero] at hzero
  have hh : S.p1+S.p2+3*S.p3=0 := by
    simpa [CyclicStaircase.residue,residueOf,hx,hy,hz] using hzero.symm
  have hrel : S.p1 = -3*S.p3-S.p2 := by linear_combination hh
  have hmap : (fun p : Point3 => S.residue (Point3.mk p.z p.y p.x)) =
      residueOf S.p3 S.p2 (-3*S.p3-S.p2) := by
    funext p
    simp only [CyclicStaircase.residue,residueOf,hrel]
    ring
  dsimp only [P] at hd
  rw [List.map_map] at hd
  change (t3r3ForcedPoints.map (fun p => S.residue (Point3.mk p.z p.y p.x))).Nodup at hd
  rw [hmap] at hd
  let a : Fin S.m := ⟨S.p3.val,ZMod.val_lt _⟩
  let b : Fin S.m := ⟨S.p2.val,ZMod.val_lt _⟩
  have hn : (t3r3EndpointResidues S.m a b).Nodup := by
    simpa only [t3r3EndpointResidues,a,b,ZMod.natCast_zmod_val] using hd
  exact t3r3_endpoint_residue_collision S.m hlo hm a b hn

/-- All ordered t=3 full-support boundaries with x=1 and at least one other unit. -/
theorem fullSupport_t3_two_unit_x_symbolic_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hu : g.y=1 ∨ g.z=1) :
    fullTarget S ≤ S.m := by
  rcases fullSupport_t3_two_unit_BW_cover S hg hf ho ht hx hu with h | ⟨hr,hs,hu⟩
  · exact h
  · by_contra hn
    have hm : S.m ≤ 30 := by
      rw [fullTarget_eq_square,hr,hs,ht] at hn
      norm_num at hn
      omega
    rcases hu with ⟨hy,hz⟩ | ⟨hy,hz⟩
    · exact t3_two_unit_131_no_go S hg hf ho ht hr hx hy hz hm
    · exact t3_two_unit_113_no_go S hg hf ho ht hr hx hy hz hm

end NSP3

