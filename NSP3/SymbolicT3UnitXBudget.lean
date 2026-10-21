import NSP3.SymbolicT3UnitXGeometry

namespace NSP3
open Finset

/-- The polynomial gap after doubling the triangular-number identities. -/
theorem t3_unit_x_square_gap_identity (r s : ℤ) :
    2*r*(r-1)+2*s*(s-1)+28*r+12*s-40-(r+s+5)^2 =
      (r-s)^2+16*r-65 := by ring

private theorem rectangle_lower (B C : ℕ) :
    B*C ≤ (ferrersRectangle 3 B C).card+3 := by
  classical
  let P := (Icc 1 B).product (Icc 1 C)
  let Q := P.filter (fun p => ¬3<p.1+p.2)
  have hsub : Q ⊆ {(1,1),(1,2),(2,1)} := by
    intro p hp
    obtain ⟨hp,hs⟩ := mem_filter.mp hp
    have h1 := mem_Icc.mp (mem_product.mp hp).1
    have h2 := mem_Icc.mp (mem_product.mp hp).2
    have he : (p.1=1 ∧ p.2=1) ∨ (p.1=1 ∧ p.2=2) ∨ (p.1=2 ∧ p.2=1) := by omega
    simpa only [mem_insert,mem_singleton,Prod.mk.injEq,Prod.ext_iff] using he
  have hq := card_le_card hsub
  norm_num at hq
  have hsplit := card_filter_add_card_filter_not (s:=P) (fun p => 3<p.1+p.2)
  have hp : P.card=B*C := by simp [P]
  change (ferrersRectangle 3 B C).card+Q.card=P.card at hsplit
  omega

/-- H and the yz rectangle are separate support resources; neither is counted twice. -/
theorem fullSupport_t3_unit_x_resource_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      3*pair12Count S.D+2*(g.y*g.z)+3*pair13Count S.D ≤ S.m+6 := by
  have hm := fullSupport_symbolic_BW_lower S hg hf ho
  have hH := t3_unit_x_H_card S hg hf ho ht hx hy hz
  have hs : 3 ≤ pair13Count S.D := by have := ho.1; omega
  have hL : pair13Count S.D-2 ≤ min (pair12Count S.D-2) (pair13Count S.D-1) := by
    have := ho.2; omega
  have hBC : 4 ≤ g.y*g.z := by nlinarith [Nat.mul_le_mul_right g.z hy]
  have hrect := rectangle_lower g.y g.z
  have hd23 : (ferrersRectangle 3 g.y g.z).card ≤ ferrersPlaneDefect 3 g.y g.z :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hd12 : 1 ≤ ferrersPlaneDefect (pair12Count S.D) g.x g.y := le_max_left _ _
  have hd13 : 1 ≤ ferrersPlaneDefect (pair13Count S.D) g.x g.z := le_max_left _ _
  have hX := le_max_left (pair12Count S.D) g.x
  have hY := le_max_left (pair12Count S.D) g.y
  have hZ := le_max_left (pair12Count S.D) g.z
  unfold fullSupportSymbolicBW at hm
  rw [hH,ht] at hm
  norm_num only [Nat.choose] at hm
  omega

/-- Terminal-return capacity converts the positive box into a uniform linear budget. -/
theorem fullSupport_t3_unit_x_coarse_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      7*pair12Count S.D+3*pair13Count S.D ≤ S.m+10 := by
  have hm := fullSupport_t3_unit_x_resource_lower S hg hf ho ht hx hy hz
  have hc := t3_unit_x_capacity S hg hf ho hx
  have ey : g.y-2+2=g.y := by omega
  have ez : g.z-2+2=g.z := by omega
  have hv : 2*pair12Count S.D ≤ g.y*g.z+2 := by
    nlinarith only [hc,ey,ez,Nat.zero_le ((g.y-2)*(g.z-2))]
  omega

theorem fullSupport_t3_unit_x_large_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z)
    (hr : 5 ≤ pair12Count S.D ∨ (pair12Count S.D=4 ∧ pair13Count S.D=3)) :
    fullTarget S ≤ S.m := by
  let r := pair12Count S.D
  let s := pair13Count S.D
  have hm := fullSupport_t3_unit_x_coarse_lower S hg hf ho ht hx hy hz
  change Nat.choose r 2+Nat.choose s 2+7*r+3*s ≤ S.m+10 at hm
  have hs : 3 ≤ s := by have := ho.1; dsimp [s]; omega
  have hsr : s ≤ r := ho.2
  have cr : 2*Nat.choose r 2=r*(r-1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have cs : 2*Nat.choose s 2=s*(s-1) := by
    rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' s.two_dvd_mul_sub_one
  have er : r-1+1=r := by omega
  have es : s-1+1=s := by omega
  have ed : r-s+s=r := Nat.sub_add_cancel hsr
  have hgap : 65 ≤ (r-s)^2+16*r := by
    rcases hr with hr | ⟨hr,ht'⟩
    · change 5 ≤ r at hr; nlinarith only [hr,Nat.zero_le ((r-s)^2)]
    · change r=4 at hr; change s=3 at ht'; simp [hr,ht']
  have hsq : (r+s+5)^2 ≤ 4*S.m := by
    nlinarith only [hm,cr,cs,er,es,ed,hgap]
  rw [fullTarget_eq_square,ht]
  change ((r+s+3+2)^2+3)/4 ≤ S.m
  have he : r+s+3+2=r+s+5 := by omega
  rw [he]; omega

private theorem small_BW_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1)
    (he : (pair12Count S.D=3 ∧ pair13Count S.D=3 ∧ g.y=2 ∧ g.z=3) ∨
      (pair12Count S.D=3 ∧ pair13Count S.D=3 ∧ g.y=3 ∧ g.z=2) ∨
      (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ g.y=2 ∧ g.z=3) ∨
      (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ g.y=3 ∧ g.z=2)) :
    fullTarget S ≤ S.m := by
  rcases he with ⟨hr,hs,hy,hz⟩ | ⟨hr,hs,hy,hz⟩ | ⟨hr,hs,hy,hz⟩ | ⟨hr,hs,hy,hz⟩
  all_goals
    have hm := fullSupport_symbolic_BW_lower S hg hf ho
    have hH := t3_unit_x_H_card S hg hf ho ht hx (by omega) (by omega)
    unfold fullSupportSymbolicBW at hm
    rw [hH] at hm
    simp only [hr,hs,ht,hx,hy,hz] at hm
    rw [fullTarget_eq_square,hr,hs,ht]
    have d1 : ferrersPlaneDefect 3 1 2=2 := by decide
    have d2 : ferrersPlaneDefect 3 1 3=1 := by decide
    have d3 : ferrersPlaneDefect 4 1 2=4 := by decide
    have d4 : ferrersPlaneDefect 4 1 3=3 := by decide
    have d5 : ferrersPlaneDefect 3 2 3=3 := by decide
    have d6 : ferrersPlaneDefect 3 3 2=3 := by decide
    norm_num [d1,d2,d3,d4,d5,d6,Nat.choose] at hm ⊢
    omega

/-- Unbounded BW coverage leaves only q333/g122. -/
theorem fullSupport_t3_unit_x_BW_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    fullTarget S ≤ S.m ∨
      (pair12Count S.D=3 ∧ pair13Count S.D=3 ∧ g.y=2 ∧ g.z=2) := by
  by_cases hr5 : 5 ≤ pair12Count S.D
  · exact Or.inl (fullSupport_t3_unit_x_large_sharp S hg hf ho ht hx hy hz (Or.inl hr5))
  have hr3 : 3 ≤ pair12Count S.D := by have := ho.1; have := ho.2; omega
  have hs3 : 3 ≤ pair13Count S.D := by have := ho.1; omega
  by_cases h43 : pair12Count S.D=4 ∧ pair13Count S.D=3
  · exact Or.inl (fullSupport_t3_unit_x_large_sharp S hg hf ho ht hx hy hz (Or.inr h43))
  have he : (pair12Count S.D=3 ∧ pair13Count S.D=3) ∨
      (pair12Count S.D=4 ∧ pair13Count S.D=4) := by have := ho.2; omega
  have hm := fullSupport_t3_unit_x_resource_lower S hg hf ho ht hx hy hz
  by_cases hv : 7 ≤ g.y*g.z
  · left
    rcases he with ⟨hr,hs⟩ | ⟨hr,hs⟩
    all_goals
      simp only [hr,hs] at hm
      norm_num [Nat.choose] at hm
      rw [fullTarget_eq_square,hr,hs,ht]
      norm_num
      omega
  have hB : g.y ≤ 3 := by nlinarith
  have hC : g.z ≤ 3 := by nlinarith
  have hbc : (g.y=2 ∧ g.z=2) ∨ (g.y=2 ∧ g.z=3) ∨ (g.y=3 ∧ g.z=2) := by
    have hn : ¬(g.y=3 ∧ g.z=3) := by rintro ⟨hb,hc⟩; simp [hb,hc] at hv
    omega
  rcases he with ⟨hr,hs⟩ | ⟨hr,hs⟩
  · rcases hbc with ⟨hb,hc⟩ | ⟨hb,hc⟩ | ⟨hb,hc⟩
    · exact Or.inr ⟨hr,hs,hb,hc⟩
    · exact Or.inl (small_BW_sharp S hg hf ho ht hx (Or.inl ⟨hr,hs,hb,hc⟩))
    · exact Or.inl (small_BW_sharp S hg hf ho ht hx (Or.inr (Or.inl ⟨hr,hs,hb,hc⟩)))
  · have hcap := t3_unit_x_capacity S hg hf ho hx
    rcases hbc with ⟨hb,hc⟩ | ⟨hb,hc⟩ | ⟨hb,hc⟩
    · omega
    · exact Or.inl (small_BW_sharp S hg hf ho ht hx (Or.inr (Or.inr (Or.inl ⟨hr,hs,hb,hc⟩))))
    · exact Or.inl (small_BW_sharp S hg hf ho ht hx (Or.inr (Or.inr (Or.inr ⟨hr,hs,hb,hc⟩))))

end NSP3
