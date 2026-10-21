import NSP3.SymbolicT3R3Budget
import NSP3.SymbolicT3R3Certificate

namespace NSP3
open Finset

/-- Membership is obtained from actual axis, triangle, punctured-core and box geometry. -/
theorem t3r3_forced_points_mem (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (h12 : pair12Count S.D = 3) (h13 : pair13Count S.D = 3)
    (h23 : pair23Count S.D = 3) (hx : g.x = 3) (hy : g.y = 1) (hz : g.z = 1) :
    ∀ p ∈ t3r3ForcedPoints, p ∈ S.D := by
  have hX := pair12_intercept1_lower S
  have hY := pair12_intercept2_lower S
  have hZ := pair12_return_capacity_fullSupport S hg hf
  have hge : g=Point3.mk 3 1 1 := Point3.ext hx hy hz
  have shape : ∀ p ∈ t3r3ForcedPoints,
      p=Point3.zero ∨ (p.y=0 ∧ p.z=0 ∧ p.x≤3) ∨
      (p.x=0 ∧ p.z=0 ∧ p.y≤3) ∨ (p.x=0 ∧ p.y=0 ∧ p.z≤3) ∨
      (0<p.x ∧ 0<p.y ∧ p.z=0 ∧ p.x+p.y≤3) ∨
      (0<p.x ∧ p.y=0 ∧ 0<p.z ∧ p.x+p.z≤3) ∨
      (p.x=0 ∧ 0<p.y ∧ 0<p.z ∧ p.y+p.z≤3) ∨
      (0<p.x ∧ 0<p.y ∧ 0<p.z ∧ p.x+p.y≤3 ∧ p.x+p.z≤3 ∧ p.y+p.z≤3) ∨
      (p.x≤3 ∧ p.y≤1 ∧ p.z≤1 ∧ p ≠ Point3.mk 3 1 1) := by decide
  intro p hp
  rcases shape p hp with he | ⟨hpy,hpz,hpx⟩ | ⟨hpx,hpz,hpy⟩ |
    ⟨hpx,hpy,hpz⟩ | ⟨hpx,hpy,hpz,hxy⟩ | ⟨hpx,hpy,hpz,hxz⟩ |
    ⟨hpx,hpy,hpz,hyz⟩ | hcore | hbox
  · simpa only [he] using S.zero_mem
  · have he : p=Point3.mk p.x 0 0 := Point3.ext rfl hpy hpz
    rw [he];exact (pure1_axis_mem_iff S _).mpr (by omega)
  · have he : p=Point3.mk 0 p.y 0 := Point3.ext hpx rfl hpz
    rw [he];exact (pure2_axis_mem_iff S _).mpr (by omega)
  · have he : p=Point3.mk 0 0 p.z := Point3.ext hpx hpy rfl
    rw [he];exact (pure3_axis_mem_iff S _).mpr (by omega)
  · have he : p=Point3.mk p.x p.y 0 := Point3.ext rfl rfl hpz
    rw [he];exact pair12Triangle_subset S.down_closed hpx hpy (by omega)
  · have he : p=Point3.mk p.x 0 p.z := Point3.ext rfl hpy rfl
    rw [he];exact pair13Triangle_subset S.down_closed hpx hpz (by omega)
  · have he : p=Point3.mk 0 p.y p.z := Point3.ext hpx rfl rfl
    rw [he];exact pair23Triangle_subset S.down_closed hpy hpz (by omega)
  · exact puncturedFullCoreFinset_subset_D S hg hf
      ((mem_puncturedFullCoreFinset _ _ _).mpr ⟨by simpa [FullCore,h12,h13,h23] using hcore,
        by intro hl;have hh:=hl.1;have := hcore.2.2.2.1;omega⟩)
  · exact lowerBoxFinset_subset_D hg ((mem_lowerBoxFinset _ _).mpr
      (by rw [hge];exact ⟨⟨hbox.1,hbox.2.1,hbox.2.2.1⟩,hbox.2.2.2⟩))

/-- The actual full-support return is zero; no terminal congruence is assumed. -/
theorem t3r3_h11_weight_relation (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (hx : g.x = 3) (hy : g.y = 1) (hz : g.z = 1) :
    S.p3 = -3*S.p1-S.p2 := by
  have h := S.residue_rho g
  rw [fullSupport_return_eq_zero S hg hf,CyclicStaircase.residue_zero] at h
  have hh : 3*S.p1+S.p2+S.p3=0 := by
    simpa [CyclicStaircase.residue,residueOf,hx,hy,hz] using h.symm
  linear_combination hh

/-- Small endpoint closed by actual return geometry and a kernel-checked congruence certificate. -/
theorem t3r3_h11_endpoint_no_go (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hr : pair12Count S.D = 3)
    (hx : g.x = 3) (hy : g.y = 1) (hz : g.z = 1) (hm : S.m ≤ 30) : False := by
  classical
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  have hs : pair13Count S.D=3 := by have:=ho.1;have:=ho.2;omega
  have hb := fullSupport_symbolic_BW_lower S hg hf ho
  rw [t3_r3_h11_BW_exact S hr hs ht (by omega) hy hz,hx] at hb
  norm_num at hb
  have hmem := t3r3_forced_points_mem S hg hf hr hs ht hx hy hz
  have hd : (t3r3ForcedPoints.map S.residue).Nodup :=
    List.Nodup.map_on (fun p hp q hq he =>
      S.standard_eq_of_residue_eq (hmem p hp) (hmem q hq) he)
      (by decide : t3r3ForcedPoints.Nodup)
  have hrel := t3r3_h11_weight_relation S hg hf hx hy hz
  let a : Fin S.m := ⟨S.p1.val,ZMod.val_lt _⟩
  let b : Fin S.m := ⟨S.p2.val,ZMod.val_lt _⟩
  have hn : (t3r3EndpointResidues S.m a b).Nodup := by
    change (t3r3ForcedPoints.map (residueOf S.p1 S.p2 S.p3)).Nodup at hd
    simpa only [t3r3EndpointResidues,a,b,ZMod.natCast_zmod_val,←hrel] using hd
  exact t3r3_endpoint_residue_collision S.m hb hm a b hn

/-- Exact canonical q333/h11 endpoint, with no extra height/weight premise. -/
theorem fullSupport_t3_h11_r3_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hr : pair12Count S.D = 3)
    (hy : g.y = 1) (hz : g.z = 1) : fullTarget S ≤ S.m := by
  have hc := pair12_terminal_return_capacity_ordered S hg hf ho
  have hx : 3 ≤ g.x := by omega
  by_cases h4 : 4 ≤ g.x
  · exact fullSupport_t3_h11_r3_height_ge4_sharp S hg hf ho ht hr h4 hy hz
  · have hh : g.x=3 := by omega
    have hs : pair13Count S.D=3 := by have:=ho.1;have:=ho.2;omega
    have htarget : fullTarget S=31 := by rw [fullTarget_eq_square,hr,hs,ht];norm_num
    by_contra hn
    have hm : S.m ≤ 30 := by omega
    exact t3r3_h11_endpoint_no_go S hg hf ho ht hr hh hy hz hm

/-- All ordered t3 h11 heights and long counts are now covered in this orientation. -/
theorem fullSupport_t3_h11_ordered_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hy : g.y = 1) (hz : g.z = 1) :
    fullTarget S ≤ S.m := by
  have hr : 3 ≤ pair12Count S.D := by have:=ho.1;have:=ho.2;omega
  by_cases h4 : 4 ≤ pair12Count S.D
  · exact fullSupport_t3_h11_ge4_sharp S hg hf ho ht h4 hy hz
  · exact fullSupport_t3_h11_r3_sharp S hg hf ho ht (by omega) hy hz

end NSP3

