import NSP3.SymbolicT3UnitYBudget

namespace NSP3
open Finset

private theorem balanced_y_cover (r A C E M T m : ℕ)
    (hr : 3 ≤ r) (hA : 2 ≤ A) (hC : 2 ≤ C) (hcap : A+C=r+1)
    (hm : 1+3*r+2*Nat.choose r 2+A*C+r+(r-1-A)+(r-2-A)+E+M+T ≤ m)
    (hE : 1 ≤ E) (hT : 1 ≤ T)
    (hMW : A+1 ≤ r → A ≤ M) (hMW2 : A+2 ≤ r → 2*A ≤ M)
    (hTail : C-2 ≤ T) (hT2 : C=2 → 2 ≤ T) :
    (2*r+5)^2 ≤ 4*m ∨ (r≤5 ∧ A=r-1 ∧ C=2) ∨ (r=4 ∧ A=2 ∧ C=3) := by
  have cr : 2*Nat.choose r 2=r*(r-1) := by
    rw [Nat.choose_two_right];exact Nat.mul_div_cancel' r.two_dvd_mul_sub_one
  have er : r-1+1=r := by omega
  have hv : 2*r ≤ A*C+2 := by
    have ea : A-2+2=A := by omega
    have ec : C-2+2=C := by omega
    have hn : 0 ≤ (A-2)*(C-2) := Nat.zero_le _
    nlinarith only [ea,ec,hn,hcap]
  by_cases hc2 : C=2
  · by_cases hr6 : 6 ≤ r
    · left
      have hM := hMW (by omega)
      have hT := hT2 hc2
      nlinarith only [hm,hv,hM,hT,hE,cr,er,hcap,hc2,hr6]
    · exact Or.inr (Or.inl ⟨by omega,by omega,hc2⟩)
  · by_cases hc3 : C=3
    · by_cases hr5 : 5 ≤ r
      · left
        have hM := hMW2 (by omega)
        nlinarith only [hm,hM,hE,hT,cr,er,hcap,hc3,hr5]
      · exact Or.inr (Or.inr ⟨by omega,by omega,hc3⟩)
    · left
      have hc4 : 4 ≤ C := by omega
      have hM := hMW (by omega)
      have e1 : r-1-A=C-2 := by omega
      have e2 : r-2-A=C-3 := by omega
      have ec2 : C-2+2=C := by omega
      have ec3 : C-3+3=C := by omega
      have hr5 : 5 ≤ r := by omega
      nlinarith only [hm,hv,hM,hTail,hE,cr,er,hcap,hc4,e1,e2,ec2,ec3,hr5]

/-- Unbounded balanced coverage leaves only four small placements, not a census. -/
theorem fullSupport_t3_unit_y_balanced_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z)
    (he : pair12Count S.D=pair13Count S.D) :
    fullTarget S ≤ S.m ∨
      (pair12Count S.D ≤ 5 ∧ g.x=pair12Count S.D-1 ∧ g.z=2) ∨
      (pair12Count S.D=4 ∧ g.x=2 ∧ g.z=3) := by
  by_cases hslack : pair12Count S.D+2 ≤ g.x+g.z
  · exact Or.inl (fullSupport_t3_unit_y_slack_sharp S hg hf ho ht hy hx hz hslack)
  let r := pair12Count S.D
  let E := (ferrersRectangle r g.x g.z).card
  let M := ferrersPlaneDefect r g.x 1
  let T := ferrersPlaneDefect 3 1 g.z
  have hcap := t3_unit_y_capacity S hg hf ho hy
  have hdiag : g.x+g.z=r+1 := by dsimp [r];omega
  have hr : 3 ≤ r := by have := ho.1;dsimp [r];omega
  have hE : 1 ≤ E := by
    apply card_pos.mpr
    exact ⟨(g.x,g.z),mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_Icc.mpr ⟨by omega,le_rfl⟩,mem_Icc.mpr ⟨by omega,le_rfl⟩⟩,by omega⟩⟩
  have hT : 1 ≤ T := le_max_left _ _
  have hMW : g.x+1 ≤ r → g.x ≤ M := by
    intro ha
    exact le_trans (ferrers_unit_W_first r g.x (by omega) ha)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hMW2 : g.x+2 ≤ r → 2*g.x ≤ M := by
    intro ha
    exact le_trans (ferrers_unit_W_two r g.x (by omega) ha)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hTail : g.z-2 ≤ T := by
    classical
    let P := (Icc 3 g.z).image (fun z => (1,z))
    have hsub : P ⊆ ferrersRectangle 3 1 g.z := by
      intro p hp
      obtain ⟨z,hz',rfl⟩ := mem_image.mp hp
      have hz' := mem_Icc.mp hz'
      exact mem_filter.mpr ⟨mem_product.mpr ⟨by simp,mem_Icc.mpr ⟨by omega,hz'.2⟩⟩,by omega⟩
    have hc : P.card=g.z-2 := by
      dsimp [P];rw [card_image_iff.mpr (fun _ _ _ _ h => congrArg Prod.snd h)];simp
    have h := card_le_card hsub
    rw [hc] at h
    exact le_trans h (le_trans (le_max_left _ _) (le_max_right _ _))
  have hT2 : g.z=2 → 2 ≤ T := by intro hz';dsimp [T];rw [hz'];decide
  have hm := fullSupport_t3_unit_y_resource_lower S hg hf ho ht hy hx hz
  have hm' : 1+3*r+2*Nat.choose r 2+g.x*g.z+r+(r-1-g.x)+(r-2-g.x)+E+M+T ≤ S.m := by
    rw [←he] at hm
    have hL : min (pair12Count S.D-2) (pair12Count S.D-1)=pair12Count S.D-2 := by omega
    rw [hL] at hm
    dsimp [r,E,M,T] at *
    omega
  rcases balanced_y_cover r g.x g.z E M T S.m hr hx hz hdiag hm' hE hT hMW hMW2 hTail hT2 with hsq | hsmall | h4
  · left
    rw [fullTarget_eq_square,←he,ht]
    change ((r+r+3+2)^2+3)/4 ≤ S.m
    have hh : r+r+3+2=2*r+5 := by omega
    rw [hh];omega
  · exact Or.inr (Or.inl hsmall)
  · exact Or.inr (Or.inr h4)

private theorem first_diagonal_y_defect (r A C : ℕ) (ha : 0 < A) (hc : 0 < C)
    (hd : A+C=r+1) : ferrersPlaneDefect r A C=1 := by
  classical
  have he : ferrersRectangle r A C = {(A,C)} := by
    ext p
    constructor
    · intro hp
      have hh := mem_filter.mp hp
      have hp' := mem_product.mp hh.1
      have hA := mem_Icc.mp hp'.1
      have hC := mem_Icc.mp hp'.2
      apply mem_singleton.mpr
      apply Prod.ext <;> omega
    · intro hp
      have heq := mem_singleton.mp hp
      subst p
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨ha,le_rfl⟩,
        mem_Icc.mpr ⟨hc,le_rfl⟩⟩,by omega⟩
  have hI : Icc A (r-C)=∅ := by apply Icc_eq_empty;omega
  simp [ferrersPlaneDefect,he,ferrersW,hI]

private theorem first_diagonal_y_BF_bonus (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z)
    (he : pair12Count S.D=pair13Count S.D)
    (hdiag : g.x+g.z=pair12Count S.D+1) : fullSupportSymbolicBW S g+2 ≤ S.m := by
  have hd := first_diagonal_y_defect (pair13Count S.D) g.x g.z hf.1 hf.2.2 (by omega)
  have hphi : 2 ≤ rankCutPhi (pair13Count S.D) g.x g.z := by
    rw [rankCutPhi_first_diagonal hf.1 hf.2.2 (by omega)]
    exact le_min hx hz
  have hr : 3 ≤ pair12Count S.D := by have := ho.1;omega
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

/-- Three balanced endpoints close by separate rank-cut and joint-axis gains. -/
theorem fullSupport_t3_unit_y_small_BF_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hy : g.y=1)
    (he : (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ g.x=3 ∧ g.z=2) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ g.x=4 ∧ g.z=2) ∨
      (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ g.x=2 ∧ g.z=3)) :
    fullTarget S ≤ S.m := by
  rcases he with ⟨hr,hs,hx,hz⟩ | ⟨hr,hs,hx,hz⟩ | ⟨hr,hs,hx,hz⟩
  all_goals
    have hbonus := first_diagonal_y_BF_bonus S hg hf ho ht hy (by omega) (by omega) (by omega) (by omega)
    have hH := t3_unit_y_H_card S hg hf ho ht hy (by omega) (by omega)
    unfold fullSupportSymbolicBW at hbonus
    rw [hH] at hbonus
    simp only [hr,hs,ht,hx,hy,hz] at hbonus
    rw [fullTarget_eq_square,hr,hs,ht]
    have hd1 : ferrersPlaneDefect 4 3 1=3 := by decide
    have hd2 : ferrersPlaneDefect 5 4 1=4 := by decide
    have hd3 : ferrersPlaneDefect 4 2 1=4 := by decide
    have hd4 : ferrersPlaneDefect 3 1 2=2 := by decide
    have hd5 : ferrersPlaneDefect 3 1 3=1 := by decide
    have hd6 : ferrersPlaneDefect 4 3 2=1 := by decide
    have hd7 : ferrersPlaneDefect 5 4 2=1 := by decide
    have hd8 : ferrersPlaneDefect 4 2 3=1 := by decide
    norm_num [hd1,hd2,hd3,hd4,hd5,hd6,hd7,hd8,Nat.choose] at hbonus ⊢
    omega

/-- The sole q333/g212 endpoint has BF lower bound30. -/
theorem fullSupport_t3_unit_y_r3_BF_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hr : pair12Count S.D=3)
    (hx : g.x=2) (hy : g.y=1) (hz : g.z=2) : 30 ≤ S.m := by
  have hs : pair13Count S.D=3 := by have := ho.1;have := ho.2;omega
  have hbonus := first_diagonal_y_BF_bonus S hg hf ho ht hy (by omega) (by omega) (by omega) (by omega)
  have hH := t3_unit_y_H_card S hg hf ho ht hy (by omega) (by omega)
  unfold fullSupportSymbolicBW at hbonus
  rw [hH] at hbonus
  simp only [hr,hs,ht,hx,hy,hz] at hbonus
  have hd1 : ferrersPlaneDefect 3 2 1=2 := by decide
  have hd2 : ferrersPlaneDefect 3 2 2=1 := by decide
  have hd3 : ferrersPlaneDefect 3 1 2=2 := by decide
  norm_num [hd1,hd2,hd3,Nat.choose] at hbonus
  exact hbonus

end NSP3
