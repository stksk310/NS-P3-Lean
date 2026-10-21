import NSP3.SymbolicT3AllNonunit

namespace NSP3
open Finset

private theorem yz_rectangle_lower (B C : ℕ) :
    B*C ≤ (ferrersRectangle 3 B C).card+3 := by
  classical
  let P := (Icc 1 B).product (Icc 1 C)
  let Q := P.filter (fun p => ¬3 < p.1+p.2)
  have hsub : Q ⊆ {(1,1),(1,2),(2,1)} := by
    intro p hp
    obtain ⟨hp,hs⟩ := mem_filter.mp hp
    have h1 := mem_Icc.mp (mem_product.mp hp).1
    have h2 := mem_Icc.mp (mem_product.mp hp).2
    have he : (p.1=1 ∧ p.2=1) ∨ (p.1=1 ∧ p.2=2) ∨ (p.1=2 ∧ p.2=1) := by omega
    simpa only [mem_insert,mem_singleton,Prod.mk.injEq,Prod.ext_iff] using he
  have hq := card_le_card hsub
  norm_num at hq
  have hsplit := card_filter_add_card_filter_not (s:=P) (fun p => 3 < p.1+p.2)
  have hp : P.card=B*C := by simp [P]
  change (ferrersRectangle 3 B C).card+Q.card=P.card at hsplit
  omega

/-- Retain the actual xy defect, without charging its baseline twice. -/
theorem fullSupport_t3_box_yz_xy_defect_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      3*pair12Count S.D+g.x*g.y*g.z+g.y*g.z+1+
      ferrersPlaneDefect (pair12Count S.D) g.x g.y ≤ S.m := by
  have hm := fullSupport_symbolic_BW_lower S hg hf ho
  have hH := positive_box_H_lower S g hf
  have hp := Nat.mul_pos (Nat.mul_pos hf.1 hf.2.1) hf.2.2
  have hrect := yz_rectangle_lower g.y g.z
  have hrectD : (ferrersRectangle 3 g.y g.z).card ≤ ferrersPlaneDefect 3 g.y g.z :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have h13 : 1 ≤ ferrersPlaneDefect (pair13Count S.D) g.x g.z := le_max_left _ _
  have hBC : 4 ≤ g.y*g.z := by nlinarith [Nat.mul_le_mul_right g.z hy]
  have hX := le_max_left (pair12Count S.D) g.x
  have hY := le_max_left (pair12Count S.D) g.y
  have hZ := le_max_left (pair12Count S.D) g.z
  unfold fullSupportSymbolicBW at hm
  rw [ht] at hm
  have hc3 : Nat.choose 3 2=3 := by decide
  rw [hc3] at hm
  omega

private theorem r5_volume_defect (A B C : ℕ) (ha : 2 ≤ A) (hb : 2 ≤ B)
    (hc : 2 ≤ C) (hcap : 7 ≤ A+B+C) :
    21 ≤ A*B*C+B*C+ferrersPlaneDefect 5 A B := by
  have hBC : 4 ≤ B*C := by nlinarith [Nat.mul_le_mul_right C hb]
  have hd : 1 ≤ ferrersPlaneDefect 5 A B := le_max_left _ _
  by_cases hA4 : 4 ≤ A
  · have hv : 4*(A+1) ≤ A*B*C+B*C := by
      calc
        _ ≤ B*C*(A+1) := Nat.mul_le_mul_right _ hBC
        _ = _ := by ring
    omega
  · have hA : A=2 ∨ A=3 := by omega
    rcases hA with rfl | rfl
    · by_cases hBC8 : 8 ≤ B*C
      · nlinarith
      · have hB : B ≤ 3 := by nlinarith [Nat.mul_le_mul_left B hc]
        have hC : C ≤ 3 := by nlinarith [Nat.mul_le_mul_right C hb]
        interval_cases B <;> interval_cases C <;> first | omega | decide
    · by_cases hBC6 : 6 ≤ B*C
      · nlinarith
      · have hB : B=2 := by nlinarith [Nat.mul_le_mul_left B hc]
        have hC : C=2 := by rw [hB] at hBC6;omega
        subst B;subst C
        decide

/-- The small long-count r=5 nonunit branch needs only volume and one Ferrers cut. -/
theorem fullSupport_t3_no_unit_r5_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hr : pair12Count S.D = 5)
    (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) : fullTarget S ≤ S.m := by
  have hcap := pair12_terminal_return_capacity_ordered S hg hf ho
  have hm := fullSupport_t3_box_yz_xy_defect_lower S hg hf ho ht hy hz
  have hv := r5_volume_defect g.x g.y g.z hx hy hz (by omega)
  rw [hr] at hm
  have hc5 : Nat.choose 5 2=10 := by decide
  rw [hc5] at hm
  have hlow : Nat.choose (pair13Count S.D) 2+47 ≤ S.m := by omega
  have hslo : 3 ≤ pair13Count S.D := by have:=ho.1;omega
  have hshi : pair13Count S.D ≤ 5 := by have:=ho.2;omega
  rw [fullTarget_eq_square,hr,ht]
  generalize hs : pair13Count S.D = s at *
  interval_cases s <;> norm_num [Nat.choose] at * <;> omega

end NSP3
