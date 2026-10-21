import NSP3.SymbolicT3SmallNonunit

namespace NSP3

/-- Keep both long-face defects in the same once-counted BW budget. -/
theorem fullSupport_t3_box_yz_two_defects_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      3*pair12Count S.D+g.x*g.y*g.z+g.y*g.z+
      ferrersPlaneDefect (pair12Count S.D) g.x g.y+
      ferrersPlaneDefect (pair13Count S.D) g.x g.z ≤ S.m := by
  have hm := fullSupport_symbolic_BW_lower S hg hf ho
  have hH := positive_box_H_lower S g hf
  have hp := Nat.mul_pos (Nat.mul_pos hf.1 hf.2.1) hf.2.2
  have hBC : 4 ≤ g.y*g.z := by nlinarith [Nat.mul_le_mul_right g.z hy]
  have h23 : g.y*g.z ≤ ferrersPlaneDefect 3 g.y g.z+3 := by
    classical
    let P := (Finset.Icc 1 g.y).product (Finset.Icc 1 g.z)
    let Q := P.filter (fun p => ¬3<p.1+p.2)
    have hq : Q ⊆ {(1,1),(1,2),(2,1)} := by
      intro p hp
      obtain ⟨hp,hs⟩ := Finset.mem_filter.mp hp
      have ha := Finset.mem_Icc.mp (Finset.mem_product.mp hp).1
      have hb := Finset.mem_Icc.mp (Finset.mem_product.mp hp).2
      have he : (p.1=1 ∧ p.2=1) ∨ (p.1=1 ∧ p.2=2) ∨ (p.1=2 ∧ p.2=1) := by omega
      simpa only [Finset.mem_insert,Finset.mem_singleton,Prod.mk.injEq,Prod.ext_iff] using he
    have hc := Finset.card_le_card hq
    norm_num at hc
    have he := Finset.card_filter_add_card_filter_not (s:=P) (fun p => 3<p.1+p.2)
    have hP : P.card=g.y*g.z := by simp [P]
    have hd : (ferrersRectangle 3 g.y g.z).card ≤ ferrersPlaneDefect 3 g.y g.z :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    change (ferrersRectangle 3 g.y g.z).card+Q.card=P.card at he
    omega
  have hX := le_max_left (pair12Count S.D) g.x
  have hY := le_max_left (pair12Count S.D) g.y
  have hZ := le_max_left (pair12Count S.D) g.z
  unfold fullSupportSymbolicBW at hm
  rw [ht] at hm
  have hc3 : Nat.choose 3 2=3 := by decide
  rw [hc3] at hm
  omega

/-- A strict failure at r=3 forces exactly the all-two box. -/
theorem fullSupport_t3_nonunit_r3_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    fullTarget S ≤ S.m ∨ g=Point3.mk 2 2 2 := by
  by_cases hsharp : fullTarget S ≤ S.m
  · exact Or.inl hsharp
  right
  have hs : pair13Count S.D=3 := by have:=ho.1;have:=ho.2;omega
  have hm := fullSupport_t3_box_yz_two_defects_lower S hg hf ho ht hy hz
  have hd12 : 1 ≤ ferrersPlaneDefect 3 g.x g.y := le_max_left _ _
  have hd13 : 1 ≤ ferrersPlaneDefect 3 g.x g.z := le_max_left _ _
  rw [hr,hs] at hm
  rw [fullTarget_eq_square,hr,hs,ht] at hsharp
  norm_num [Nat.choose] at hm hsharp
  have hBC : 4 ≤ g.y*g.z := by nlinarith [Nat.mul_le_mul_right g.z hy]
  have hv : 4*(g.x+1) ≤ g.x*g.y*g.z+g.y*g.z := by
    calc
      _ ≤ g.y*g.z*(g.x+1) := Nat.mul_le_mul_right _ hBC
      _ = _ := by ring
  have heX : g.x=2 := by omega
  have heY : g.y=2 := by rw [heX] at hm; nlinarith [Nat.mul_le_mul_left g.y hz]
  have heZ : g.z=2 := by rw [heX,heY] at hm;omega
  exact Point3.ext heX heY heZ

/-- r=4 leaves only the actual q443/g322 singleton, not an atlas assumption. -/
theorem fullSupport_t3_nonunit_r4_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=4)
    (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    fullTarget S ≤ S.m ∨ (pair13Count S.D=4 ∧ g=Point3.mk 3 2 2) := by
  by_cases hsharp : fullTarget S ≤ S.m
  · exact Or.inl hsharp
  right
  have hslo : 3 ≤ pair13Count S.D := by have:=ho.1;omega
  have hshi : pair13Count S.D ≤ 4 := by have:=ho.2;omega
  have hm := fullSupport_t3_box_yz_two_defects_lower S hg hf ho ht hy hz
  have hd12 : 1 ≤ ferrersPlaneDefect 4 g.x g.y := le_max_left _ _
  have hd13 : 1 ≤ ferrersPlaneDefect (pair13Count S.D) g.x g.z := le_max_left _ _
  rw [hr] at hm
  have htarget : fullTarget S ≤ 43 := by
    rw [fullTarget_eq_square,hr,ht]
    generalize he : pair13Count S.D=s at *
    interval_cases s <;> norm_num
  have hm42 : S.m ≤ 42 := by omega
  have hc3 : 3 ≤ Nat.choose (pair13Count S.D) 2 := by
    generalize he : pair13Count S.D=s at *
    interval_cases s <;> decide
  have hc4 : Nat.choose 4 2=6 := by decide
  rw [hc4] at hm
  have hBC : 4 ≤ g.y*g.z := by nlinarith [Nat.mul_le_mul_right g.z hy]
  have hv : 4*(g.x+1) ≤ g.x*g.y*g.z+g.y*g.z := by
    calc
      _ ≤ g.y*g.z*(g.x+1) := Nat.mul_le_mul_right _ hBC
      _ = _ := by ring
  have hA3 : g.x ≤ 3 := by omega
  have hBC7 : g.y*g.z ≤ 7 := by nlinarith [Nat.mul_le_mul_right (g.y*g.z) hx]
  have hB3 : g.y ≤ 3 := by nlinarith [Nat.mul_le_mul_left g.y hz]
  have hC3 : g.z ≤ 3 := by nlinarith [Nat.mul_le_mul_right g.z hy]
  have d322 : ferrersPlaneDefect 3 2 2=1 := by decide
  have d323 : ferrersPlaneDefect 3 2 3=3 := by decide
  have d332 : ferrersPlaneDefect 3 3 2=3 := by decide
  have d333 : ferrersPlaneDefect 3 3 3=6 := by decide
  have d422 : ferrersPlaneDefect 4 2 2=4 := by decide
  have d423 : ferrersPlaneDefect 4 2 3=1 := by decide
  have d432 : ferrersPlaneDefect 4 3 2=1 := by decide
  have d433 : ferrersPlaneDefect 4 3 3=3 := by decide
  rw [fullTarget_eq_square,hr,ht] at hsharp
  generalize hs : pair13Count S.D=s at *
  generalize hA : g.x=A at *
  generalize hB : g.y=B at *
  generalize hC : g.z=C at *
  interval_cases s <;> interval_cases A <;> interval_cases B <;> interval_cases C
  all_goals simp only [d322,d323,d332,d333,d422,d423,d432,d433] at hm
  all_goals norm_num [Nat.choose] at hm hsharp
  all_goals first | omega | exact ⟨rfl,Point3.ext hA hB hC⟩

end NSP3
