import NSP3.SymbolicT3H11Integration

namespace NSP3
open Finset

private theorem rectangle_row_three (A : ℕ) :
    (ferrersRectangle 3 A 1).card = A-2 := by
  classical
  have he : ferrersRectangle 3 A 1 = (Icc 3 A).image (fun x => (x,1)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨hprod,hs⟩ := mem_filter.mp hp
      obtain ⟨ha,hb⟩ := mem_product.mp hprod
      have ha' := mem_Icc.mp ha
      have hb' := mem_Icc.mp hb
      exact mem_image.mpr ⟨p.1,mem_Icc.mpr ⟨by omega,ha'.2⟩,
        Prod.ext rfl (by omega)⟩
    · intro hp
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
      have hx' := mem_Icc.mp hx
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨by omega,hx'.2⟩,
        by simp⟩,by omega⟩
  rw [he,card_image_iff.mpr (fun _ _ _ _ h => congrArg Prod.fst h)]
  simp

/-- The long unit face has no W-cut and exactly h-2 rectangle points. -/
theorem t3_r3_h11_face_defect (h : ℕ) (hh : 3 ≤ h) :
    ferrersPlaneDefect 3 h 1 = max 1 (h-2) := by
  have he : Icc h (3-1) = ∅ := by apply Icc_eq_empty;omega
  simp [ferrersPlaneDefect,rectangle_row_three,ferrersW,he]

/-- Actual H consists of one variable row and two off-row points. -/
theorem t3_r3_h11_H_card (S : CyclicStaircase) {g : Point3}
    (h12 : pair12Count S.D = 3) (h13 : pair13Count S.D = 3)
    (h23 : pair23Count S.D = 3) (hx : 3 ≤ g.x) (hy : g.y = 1) (hz : g.z = 1) :
    (fullSupportSymbolicH S g).card = g.x + 1 := by
  classical
  let R := (Icc 1 (g.x-1)).image (fun x => Point3.mk x 1 1)
  have he : fullSupportSymbolicH S g =
      insert (Point3.mk 1 2 1) (insert (Point3.mk 1 1 2) R) := by
    ext p
    simp only [fullSupportSymbolicH,mem_union,mem_puncturedFullCoreFinset,
      mem_filter,mem_lowerBoxFinset,mem_insert]
    constructor
    · rintro (⟨hc,hn⟩ | ⟨⟨hle,hne⟩,hf⟩)
      · simp only [FullCore,h12,h13,h23] at hc
        by_cases hpY : p.y=2
        · left;apply Point3.ext <;> simp <;> omega
        · by_cases hpZ : p.z=2
          · right;left;apply Point3.ext <;> simp <;> omega
          · right;right
            exact mem_image.mpr ⟨p.x,mem_Icc.mpr ⟨hc.1,by omega⟩,
              by apply Point3.ext <;> simp <;> omega⟩
      · have hpY : p.y=1 := by have := hle.2.1;have := hf.2.1;omega
        have hpZ : p.z=1 := by have := hle.2.2;have := hf.2.2;omega
        have hpX : p.x < g.x := by
          have := hle.1
          by_contra hn
          apply hne
          apply Point3.ext <;> omega
        right;right
        exact mem_image.mpr ⟨p.x,mem_Icc.mpr ⟨hf.1,by omega⟩,
          by apply Point3.ext <;> simp_all⟩
    · rintro (rfl | rfl | hp)
      · left
        refine ⟨?_,?_⟩
        · simp [FullCore,h12,h13,h23]
        · intro hl;have := hl.1;change g.x ≤ 1 at this;omega
      · left
        refine ⟨?_,?_⟩
        · simp [FullCore,h12,h13,h23]
        · intro hl;have := hl.1;change g.x ≤ 1 at this;omega
      · obtain ⟨x,hmem,rfl⟩ := mem_image.mp hp
        have hm := mem_Icc.mp hmem
        right
        refine ⟨⟨⟨by change x ≤ g.x;omega,by simp [hy],by simp [hz]⟩,?_⟩,?_⟩
        · intro h;have := congrArg Point3.x h;change x=g.x at this;omega
        · simp [FullSupport];omega
  have hn1 : Point3.mk 1 1 2 ∉ R := by
    intro hp;obtain ⟨x,_,hh⟩ := mem_image.mp hp
    have := congrArg Point3.z hh;norm_num at this
  have hn2 : Point3.mk 1 2 1 ∉ insert (Point3.mk 1 1 2) R := by
    simp only [mem_insert,not_or]
    constructor
    · intro hh;have := congrArg Point3.y hh;norm_num at this
    · intro hp;obtain ⟨x,_,hh⟩ := mem_image.mp hp
      have := congrArg Point3.y hh;norm_num at this
  have hc : R.card = g.x-1 := by
    dsimp [R]
    rw [card_image_iff.mpr (fun _ _ _ _ h => congrArg Point3.x h)]
    simp
  rw [he,card_insert_of_notMem hn2,card_insert_of_notMem hn1,hc]
  omega

/-- Exact frozen BW, including the h=3 maximum/subtraction boundary. -/
theorem t3_r3_h11_BW_exact (S : CyclicStaircase) {g : Point3}
    (h12 : pair12Count S.D = 3) (h13 : pair13Count S.D = 3)
    (h23 : pair23Count S.D = 3) (hx : 3 ≤ g.x) (hy : g.y = 1) (hz : g.z = 1) :
    fullSupportSymbolicBW S g = 2*g.x + 19 + 2*max 1 (g.x-2) := by
  have hH := t3_r3_h11_H_card S h12 h13 h23 hx hy hz
  have hd : ferrersPlaneDefect 3 1 1=2 := by decide
  unfold fullSupportSymbolicBW
  rw [hH,h12,h13,h23,hy,hz,t3_r3_h11_face_defect _ hx,hd]
  simp only [max_eq_right hx]
  norm_num
  omega

/-- Exact small-height budget; it is 27, not the sharp target 31. -/
theorem t3_r3_h11_BW_height3 (S : CyclicStaircase) {g : Point3}
    (h12 : pair12Count S.D=3) (h13 : pair13Count S.D=3) (h23 : pair23Count S.D=3)
    (hx : g.x=3) (hy : g.y=1) (hz : g.z=1) : fullSupportSymbolicBW S g=27 := by
  rw [t3_r3_h11_BW_exact S h12 h13 h23 (by omega) hy hz,hx]
  decide

/-- The exact affine closed form on every height at least four. -/
theorem t3_r3_h11_BW_height_ge4 (S : CyclicStaircase) {g : Point3}
    (h12 : pair12Count S.D=3) (h13 : pair13Count S.D=3) (h23 : pair23Count S.D=3)
    (hx : 4 ≤ g.x) (hy : g.y=1) (hz : g.z=1) :
    fullSupportSymbolicBW S g=4*g.x+15 := by
  rw [t3_r3_h11_BW_exact S h12 h13 h23 (by omega) hy hz]
  omega

/-- No actual staircase with h>=4 can be a strict counterexample. -/
theorem fullSupport_t3_h11_r3_height_ge4_sharp (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hr : pair12Count S.D = 3)
    (hx : 4 ≤ g.x) (hy : g.y = 1) (hz : g.z = 1) : fullTarget S ≤ S.m := by
  have hs : pair13Count S.D=3 := by have := ho.1;have := ho.2;omega
  have hb := fullSupport_symbolic_BW_lower S hg hf ho
  rw [t3_r3_h11_BW_exact S hr hs ht (by omega) hy hz] at hb
  rw [fullTarget_eq_square,hr,hs,ht]
  norm_num
  omega

end NSP3
