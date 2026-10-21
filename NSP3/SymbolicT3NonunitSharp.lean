import NSP3.SymbolicT3NonunitCoverage
import NSP3.SymbolicT3NonunitCertificate

namespace NSP3

def T3SmallForcedShape (r s t : ℕ) (g p : Point3) : Prop :=
  p = Point3.zero ∨ (p.y = 0 ∧ p.z = 0 ∧ p.x ≤ r) ∨
  (p.x = 0 ∧ p.z = 0 ∧ p.y ≤ r) ∨ (p.x = 0 ∧ p.y = 0 ∧ p.z ≤ r) ∨
  (0 < p.x ∧ 0 < p.y ∧ p.z = 0 ∧ p.x+p.y ≤ r) ∨
  (0 < p.x ∧ p.y = 0 ∧ 0 < p.z ∧ p.x+p.z ≤ s) ∨
  (p.x = 0 ∧ 0 < p.y ∧ 0 < p.z ∧ p.y+p.z ≤ t) ∨
  (p.x ≤ g.x ∧ p.y ≤ g.y ∧ p.z ≤ g.z ∧ p ≠ g)

/-- Uniform actual geometric membership, independent of small moduli. -/
theorem t3_small_forced_shape_mem (S : CyclicStaircase) {g p : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (hp : T3SmallForcedShape (pair12Count S.D) (pair13Count S.D) (pair23Count S.D) g p) :
    p ∈ S.D := by
  have hX := pair12_intercept1_lower S
  have hY := pair12_intercept2_lower S
  have hZ := pair12_return_capacity_fullSupport S hg hf
  rcases hp with he | ⟨hpy,hpz,hpx⟩ | ⟨hpx,hpz,hpy⟩ |
    ⟨hpx,hpy,hpz⟩ | ⟨hpx,hpy,hpz,hxy⟩ | ⟨hpx,hpy,hpz,hxz⟩ |
    ⟨hpx,hpy,hpz,hyz⟩ | hbox
  · simpa only [he] using S.zero_mem
  · have he : p=Point3.mk p.x 0 0 := Point3.ext rfl hpy hpz
    rw [he];exact (pure1_axis_mem_iff S _).mpr (by omega)
  · have he : p=Point3.mk 0 p.y 0 := Point3.ext hpx rfl hpz
    rw [he];exact (pure2_axis_mem_iff S _).mpr (by omega)
  · have he : p=Point3.mk 0 0 p.z := Point3.ext hpx hpy rfl
    rw [he];exact (pure3_axis_mem_iff S _).mpr (by omega)
  · have he : p=Point3.mk p.x p.y 0 := Point3.ext rfl rfl hpz
    rw [he];exact pair12Triangle_subset S.down_closed hpx hpy hxy
  · have he : p=Point3.mk p.x 0 p.z := Point3.ext rfl hpy rfl
    rw [he];exact pair13Triangle_subset S.down_closed hpx hpz hxz
  · have he : p=Point3.mk 0 p.y p.z := Point3.ext hpx rfl rfl
    rw [he];exact pair23Triangle_subset S.down_closed hpy hpz hyz
  · exact lowerBoxFinset_subset_D hg ((mem_lowerBoxFinset _ _).mpr
      ⟨⟨hbox.1,hbox.2.1,hbox.2.2.1⟩,hbox.2.2.2⟩)

private theorem forced_certificate_no_go (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (P : List Point3)
    (hmem : ∀ p ∈ P, p ∈ S.D) (hnd : P.Nodup)
    (hcert : ∀ a b c : Fin S.m,
      residueOf (a.val : ZMod S.m) (b.val : ZMod S.m) (c.val : ZMod S.m) g=0 →
      ¬ (t3SmallResidues S.m a b c P).Nodup) : False := by
  letI : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  have hzero := S.residue_rho g
  rw [fullSupport_return_eq_zero S hg hf,CyclicStaircase.residue_zero] at hzero
  change 0 = residueOf S.p1 S.p2 S.p3 g at hzero
  have hd : (P.map S.residue).Nodup := List.Nodup.map_on
    (fun p hp q hq he => S.standard_eq_of_residue_eq (hmem p hp) (hmem q hq) he) hnd
  let a : Fin S.m := ⟨S.p1.val,ZMod.val_lt _⟩
  let b : Fin S.m := ⟨S.p2.val,ZMod.val_lt _⟩
  let c : Fin S.m := ⟨S.p3.val,ZMod.val_lt _⟩
  have hz : residueOf (a.val : ZMod S.m) (b.val : ZMod S.m) (c.val : ZMod S.m) g=0 := by
    simpa only [a,b,c,ZMod.natCast_zmod_val] using hzero.symm
  have hn : (t3SmallResidues S.m a b c P).Nodup := by
    change (P.map (residueOf S.p1 S.p2 S.p3)).Nodup at hd
    simpa only [t3SmallResidues,a,b,c,ZMod.natCast_zmod_val] using hd
  exact hcert a b c hz hn

/-- q333/g222 is impossible below 31, using all weights and no normalization. -/
theorem t3_nonunit_r3_endpoint_no_go (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (he : g=Point3.mk 2 2 2) (hm : S.m ≤ 30) : False := by
  have hs : pair13Count S.D=3 := by have:=ho.1;have:=ho.2;omega
  have hmem : ∀ p ∈ t3r3NonunitPoints,p ∈ S.D := by
    intro p hp
    apply t3_small_forced_shape_mem S hg hf
    rw [hr,hs,ht,he]
    have hshape : ∀ p ∈ t3r3NonunitPoints,T3SmallForcedShape 3 3 3 (Point3.mk 2 2 2) p := by
      unfold T3SmallForcedShape
      decide
    exact hshape p hp
  have hc : 29 ≤ S.m := by
    have h := Finset.card_le_card (show t3r3NonunitPoints.toFinset ⊆ S.D by
      intro p hp;exact hmem p (List.mem_toFinset.mp hp))
    have hn : t3r3NonunitPoints.toFinset.card=29 := by decide
    rw [hn,S.card_D] at h
    exact h
  apply forced_certificate_no_go S hg hf t3r3NonunitPoints hmem (by decide)
  have hemod : S.m=29 ∨ S.m=30 := by omega
  rcases hemod with hm29 | hm30
  · rw [hm29,he]
    simpa only [residueOf,Nat.cast_ofNat] using t3r3NonunitPoints_collision_29
  · rw [hm30,he]
    simpa only [residueOf,Nat.cast_ofNat] using t3r3NonunitPoints_collision_30

/-- q443/g322 has 42 forced standard points but admits no cyclic residue injection. -/
theorem t3_nonunit_r4_endpoint_no_go (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=4) (hs : pair13Count S.D=4)
    (he : g=Point3.mk 3 2 2) (hm : S.m ≤ 42) : False := by
  have hmem : ∀ p ∈ t3r4NonunitPoints,p ∈ S.D := by
    intro p hp
    apply t3_small_forced_shape_mem S hg hf
    rw [hr,hs,ht,he]
    have hshape : ∀ p ∈ t3r4NonunitPoints,T3SmallForcedShape 4 4 3 (Point3.mk 3 2 2) p := by
      unfold T3SmallForcedShape
      decide
    exact hshape p hp
  have hc : 42 ≤ S.m := by
    have h := Finset.card_le_card (show t3r4NonunitPoints.toFinset ⊆ S.D by
      intro p hp;exact hmem p (List.mem_toFinset.mp hp))
    have hn : t3r4NonunitPoints.toFinset.card=42 := by decide
    rw [hn,S.card_D] at h
    exact h
  have hm42 : S.m=42 := by omega
  apply forced_certificate_no_go S hg hf t3r4NonunitPoints hmem (by decide)
  rw [hm42,he]
  simpa only [residueOf,Nat.cast_ofNat] using t3r4NonunitPoints_collision_42

/-- All ordered t3 with three nonunit coordinates, including r=3,4,5. -/
theorem fullSupport_t3_nonunit_ordered_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    fullTarget S ≤ S.m := by
  have hr : 3 ≤ pair12Count S.D := by have:=ho.1;have:=ho.2;omega
  by_cases h6 : 6 ≤ pair12Count S.D
  · exact fullSupport_t3_no_unit_ge6_sharp S hg hf ho ht h6 hx hy hz
  by_cases h5 : pair12Count S.D=5
  · exact fullSupport_t3_no_unit_r5_sharp S hg hf ho ht h5 hx hy hz
  by_cases h4 : pair12Count S.D=4
  · rcases fullSupport_t3_nonunit_r4_cover S hg hf ho ht h4 hx hy hz with h | ⟨hs,he⟩
    · exact h
    · by_contra hn
      have hm : S.m ≤ 42 := by rw [fullTarget_eq_square,h4,hs,ht] at hn;norm_num at hn;omega
      exact t3_nonunit_r4_endpoint_no_go S hg hf ht h4 hs he hm
  · have h3 : pair12Count S.D=3 := by omega
    rcases fullSupport_t3_nonunit_r3_cover S hg hf ho ht h3 hx hy hz with h | he
    · exact h
    · by_contra hn
      have hs : pair13Count S.D=3 := by have:=ho.1;have:=ho.2;omega
      have hm : S.m ≤ 30 := by rw [fullTarget_eq_square,h3,hs,ht] at hn;norm_num at hn;omega
      exact t3_nonunit_r3_endpoint_no_go S hg hf ho ht h3 he hm

end NSP3
