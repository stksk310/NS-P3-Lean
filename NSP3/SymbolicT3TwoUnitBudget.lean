import NSP3.SymbolicT3TwoUnitGeometry

namespace NSP3
open Finset

/-- Two distinct endpoint columns each contribute one. -/
theorem two_unit_W_ge_two (n : ℕ) (hn : 3 ≤ n) : 2 ≤ ferrersW n 1 1 := by
  have hsub : ({1,n-1} : Finset ℕ) ⊆ Icc 1 (n-1) := by
    intro i hi
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl | rfl <;> exact mem_Icc.mpr ⟨by omega,by omega⟩
  have hs := sum_le_sum_of_subset_of_nonneg (f:=fun i=>min (n-i) i)
    hsub (by intros;exact Nat.zero_le _)
  simp only [sum_insert (by simp;omega : (1:ℕ) ∉ ({n-1}:Finset ℕ)),sum_singleton] at hs
  change 2 ≤ (Icc 1 (n-1)).sum (fun i=>min (1*(n-i)) (1*i))
  simp only [one_mul]
  omega

/-- A third disjoint column contributes two once n>=4. -/
theorem two_unit_W_ge_four (n : ℕ) (hn : 4 ≤ n) : 4 ≤ ferrersW n 1 1 := by
  have hsub : ({1,2,n-1} : Finset ℕ) ⊆ Icc 1 (n-1) := by
    intro i hi
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl | rfl | rfl <;> exact mem_Icc.mpr ⟨by omega,by omega⟩
  have hs := sum_le_sum_of_subset_of_nonneg (f:=fun i=>min (n-i) i)
    hsub (by intros;exact Nat.zero_le _)
  simp only [sum_insert (by simp;omega : (1:ℕ) ∉ ({2,n-1}:Finset ℕ)),
    sum_insert (by simp;omega : (2:ℕ) ∉ ({n-1}:Finset ℕ)),sum_singleton] at hs
  change 4 ≤ (Icc 1 (n-1)).sum (fun i=>min (1*(n-i)) (1*i))
  simp only [one_mul]
  omega

private theorem rectangle_left (n h : ℕ) (hn : 1 ≤ n) :
    (ferrersRectangle n 1 h).card=h+1-n := by
  classical
  have he : ferrersRectangle n 1 h=(Icc n h).image (fun a=>(1,a)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp,hs⟩ := mem_filter.mp hp
      obtain ⟨ha,hb⟩ := mem_product.mp hp
      have ha := mem_Icc.mp ha; have hb := mem_Icc.mp hb
      exact mem_image.mpr ⟨p.2,mem_Icc.mpr ⟨by omega,hb.2⟩,Prod.ext (by omega) rfl⟩
    · intro hp
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hp
      have ha := mem_Icc.mp ha
      exact mem_filter.mpr ⟨mem_product.mpr ⟨by simp,mem_Icc.mpr ⟨by omega,ha.2⟩⟩,by omega⟩
  rw [he,card_image_iff.mpr (fun _ _ _ _ h=>congrArg Prod.snd h)]
  simp [Nat.card_Icc]

private theorem rectangle_right (n h : ℕ) (hn : 1 ≤ n) :
    (ferrersRectangle n h 1).card=h+1-n := by
  classical
  have he : ferrersRectangle n h 1=(Icc n h).image (fun a=>(a,1)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp,hs⟩ := mem_filter.mp hp
      obtain ⟨ha,hb⟩ := mem_product.mp hp
      have ha := mem_Icc.mp ha; have hb := mem_Icc.mp hb
      exact mem_image.mpr ⟨p.1,mem_Icc.mpr ⟨by omega,ha.2⟩,Prod.ext rfl (by omega)⟩
    · intro hp
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hp
      have ha := mem_Icc.mp ha
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,ha.2⟩,by simp⟩,by omega⟩
  rw [he,card_image_iff.mpr (fun _ _ _ _ h=>congrArg Prod.fst h)]
  simp [Nat.card_Icc]

theorem two_unit_defect_long_left (n h : ℕ) (hn : 3 ≤ n) (hh : n ≤ h) :
    ferrersPlaneDefect n 1 h=h-n+1 := by
  have he : Icc 1 (n-h)=∅ := by apply Icc_eq_empty;omega
  simp only [ferrersPlaneDefect,rectangle_left n h (by omega),ferrersW,he,sum_empty]
  omega

theorem two_unit_defect_long_right (n h : ℕ) (hn : 3 ≤ n) (hh : n ≤ h) :
    ferrersPlaneDefect n h 1=h-n+1 := by
  have he : Icc h (n-1)=∅ := by apply Icc_eq_empty;omega
  simp only [ferrersPlaneDefect,rectangle_right n h (by omega),ferrersW,he,sum_empty]
  omega

theorem two_unit_defect_unit (n : ℕ) (hn : 3 ≤ n) :
    ferrersPlaneDefect n 1 1=ferrersW n 1 1 := by
  have hw := two_unit_W_ge_two n hn
  have hr := rectangle_left n 1 (by omega)
  unfold ferrersPlaneDefect
  rw [hr]
  have hzero : 1+1-n=0 := by omega
  rw [hzero]
  omega

/-- Guarded exact BW, retaining the original disjoint support accounting. -/
theorem t3_two_unit_1h1_BW_exact (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hz : g.z=1) :
    fullSupportSymbolicBW S g+3 = Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+pair12Count S.D+2*pair13Count S.D+
      min (pair12Count S.D-2) (pair13Count S.D-1)+4*g.y+ferrersW (pair13Count S.D) 1 1 := by
  have hc := pair12_terminal_return_capacity_ordered S hg hf ho
  have hs : 3 ≤ pair13Count S.D := by have := ho.1;omega
  have hr : 3 ≤ pair12Count S.D := by have := ho.2;omega
  have hh : pair12Count S.D ≤ g.y := by omega
  have hh' : pair13Count S.D ≤ g.y := le_trans ho.2 hh
  have hH := t3_two_unit_H_card S hg hf ho ht hx (Or.inr hz)
  unfold fullSupportSymbolicBW
  rw [hx,hz,ht,two_unit_defect_long_left _ _ hr hh,two_unit_defect_unit _ hs,
    two_unit_defect_long_right _ _ (by omega) (by omega)]
  rw [max_eq_left (by omega : 1 ≤ pair12Count S.D),max_eq_right hh]
  norm_num only [Nat.choose]
  omega

theorem t3_two_unit_11h_BW_exact (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : g.y=1) :
    fullSupportSymbolicBW S g+3 = Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+2*pair12Count S.D+pair13Count S.D+
      min (pair12Count S.D-2) (pair13Count S.D-1)+4*g.z+ferrersW (pair12Count S.D) 1 1 := by
  have hc := pair12_terminal_return_capacity_ordered S hg hf ho
  have hs : 3 ≤ pair13Count S.D := by have := ho.1;omega
  have hr : 3 ≤ pair12Count S.D := by have := ho.2;omega
  have hh : pair12Count S.D ≤ g.z := by omega
  have hh' : pair13Count S.D ≤ g.z := le_trans ho.2 hh
  have hH := t3_two_unit_H_card S hg hf ho ht hx (Or.inl hy)
  unfold fullSupportSymbolicBW
  rw [hx,hy,ht,two_unit_defect_unit _ hr,two_unit_defect_long_left _ _ hs hh',
    two_unit_defect_long_left _ _ (by omega) (by omega)]
  rw [max_eq_left (by omega : 1 ≤ pair12Count S.D),max_eq_right hh]
  norm_num only [Nat.choose]
  omega

end NSP3
