import NSP3.SymbolicT3UnitCover

namespace NSP3
open Finset

private theorem first_diagonal_defect (r A B : ℕ) (ha : 0 < A) (hb : 0 < B)
    (hd : A+B=r+1) : ferrersPlaneDefect r A B=1 := by
  classical
  have he : ferrersRectangle r A B = {(A,B)} := by
    ext p
    constructor
    · intro hp
      have hh := Finset.mem_filter.mp hp
      have hp' := Finset.mem_product.mp hh.1
      have hA := Finset.mem_Icc.mp hp'.1
      have hB := Finset.mem_Icc.mp hp'.2
      apply Finset.mem_singleton.mpr
      apply Prod.ext <;> omega
    · intro hp
      have heq := Finset.mem_singleton.mp hp
      subst p
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨ha,le_rfl⟩,
        Finset.mem_Icc.mpr ⟨hb,le_rfl⟩⟩,by omega⟩
  have hI : Icc A (r-B) = ∅ := by apply Icc_eq_empty;omega
  simp [ferrersPlaneDefect,he,ferrersW,hI]

/-- Rank-cut contributes a plane unit and joint-axis contributes one distinct unit. -/
private theorem first_diagonal_BF_bonus (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hz : g.z=1) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y)
    (hdiag : g.x+g.y=pair12Count S.D+1) : fullSupportSymbolicBW S g+2 ≤ S.m := by
  have hd := first_diagonal_defect (pair12Count S.D) g.x g.y hf.1 hf.2.1 hdiag
  have hphi : 2 ≤ rankCutPhi (pair12Count S.D) g.x g.y := by
    rw [rankCutPhi_first_diagonal hf.1 hf.2.1 hdiag]
    exact le_min hx hy
  have hr : 3 ≤ pair12Count S.D := by have := ho.1;have := ho.2;omega
  have hGain : 1 ≤ fullSupportAxisGain S g := by
    unfold fullSupportAxisGain jointAxisGain
    dsimp only
    rw [max_eq_left (show g.x ≤ pair12Count S.D by omega),
      max_eq_left (show g.y ≤ pair12Count S.D by omega),
      max_eq_left (show g.z ≤ pair12Count S.D by omega)]
    omega
  have hm := fullSupport_symbolic_BF_lower S hg hf ho
  unfold fullSupportSymbolicBF at hm
  rw [hd] at hm
  omega

/-- Four small z-unit placements close by BF, without a modular census. -/
theorem fullSupport_t3_unit_z_small_BF_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hz : g.z=1)
    (he : (pair12Count S.D=4 ∧ pair13Count S.D=3 ∧ g.x=2 ∧ g.y=3) ∨
      (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ g.x=3 ∧ g.y=2) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ g.x=4 ∧ g.y=2) ∨
      (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ g.x=2 ∧ g.y=3)) : fullTarget S ≤ S.m := by
  rcases he with ⟨hr,hs,hx,hy⟩ | ⟨hr,hs,hx,hy⟩ | ⟨hr,hs,hx,hy⟩ | ⟨hr,hs,hx,hy⟩
  all_goals
    have hbonus := first_diagonal_BF_bonus S hg hf ho ht hz (by omega) (by omega) (by omega)
    have hH := t3_unit_z_H_card S hg hf ho ht hz (by omega) (by omega)
    unfold fullSupportSymbolicBW at hbonus
    rw [hH,hr,hs,ht,hx,hy,hz] at hbonus
    rw [fullTarget_eq_square,hr,hs,ht]
    norm_num at hbonus ⊢
    have hd1 : ferrersPlaneDefect 4 2 3 = 1 := by decide
    have hd2 : ferrersPlaneDefect 3 2 1 = 2 := by decide
    have hd3 : ferrersPlaneDefect 3 3 1 = 1 := by decide
    have hd4 : ferrersPlaneDefect 4 3 2 = 1 := by decide
    have hd5 : ferrersPlaneDefect 4 3 1 = 3 := by decide
    have hd6 : ferrersPlaneDefect 5 4 2 = 1 := by decide
    have hd7 : ferrersPlaneDefect 5 4 1 = 4 := by decide
    have hd8 : ferrersPlaneDefect 4 2 1 = 4 := by decide
    norm_num [hd1,hd2,hd3,hd4,hd5,hd6,hd7,hd8,Nat.choose] at hbonus ⊢
    omega

/-- The only remaining small endpoint has actual BF lower bound30, not28. -/
theorem fullSupport_t3_unit_z_r3_BF_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=2) (hy : g.y=2) (hz : g.z=1) : 30 ≤ S.m := by
  have hs : pair13Count S.D=3 := by have := ho.1;have := ho.2;omega
  have hbonus := first_diagonal_BF_bonus S hg hf ho ht hz (by omega) (by omega) (by omega)
  have hH := t3_unit_z_H_card S hg hf ho ht hz (by omega) (by omega)
  unfold fullSupportSymbolicBW at hbonus
  rw [hH,hr,hs,ht,hx,hy,hz] at hbonus
  norm_num [ferrersPlaneDefect,ferrersRectangle,ferrersW] at hbonus
  exact hbonus

end NSP3
