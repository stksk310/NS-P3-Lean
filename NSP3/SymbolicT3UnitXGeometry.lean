import NSP3.SymbolicT3UnitYGeometry

namespace NSP3
open Finset

/-- Capacity on the x-unit face comes from the actual terminal return. -/
theorem t3_unit_x_capacity (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hx : g.x=1) : pair12Count S.D+1 ≤ g.y+g.z := by
  have h := pair12_terminal_return_capacity_ordered S hg hf ho
  omega

private def xRow (lo hi y z : ℕ) : Finset Point3 :=
  (Icc lo hi).image (fun x => Point3.mk x y z)

private theorem mem_xRow (lo hi y z : ℕ) (p : Point3) :
    p ∈ xRow lo hi y z ↔ lo ≤ p.x ∧ p.x ≤ hi ∧ p.y=y ∧ p.z=z := by
  constructor
  · intro hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    exact ⟨(mem_Icc.mp hx).1,(mem_Icc.mp hx).2,rfl,rfl⟩
  · rintro ⟨hl,hu,hy,hz⟩
    exact mem_image.mpr ⟨p.x,mem_Icc.mpr ⟨hl,hu⟩,by ext <;> simp_all⟩

private theorem card_xRow (lo hi y z : ℕ) :
    (xRow lo hi y z).card=hi+1-lo := by
  unfold xRow
  rw [card_image_iff.mpr (fun _ _ _ _ h => congrArg Point3.x h)]
  simp

private theorem unit_x_box_card (g : Point3) (hx : g.x=1)
    (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    (by classical exact ((lowerBoxFinset g).filter FullSupport).card=g.y*g.z-1) := by
  classical
  let P := (Icc 1 g.y).product (Icc 1 g.z)
  let f : ℕ × ℕ → Point3 := fun p => Point3.mk 1 p.1 p.2
  have hi : Set.InjOn f P := by
    intro a _ b _ h
    exact Prod.ext (congrArg Point3.y h) (congrArg Point3.z h)
  have hgmem : g ∈ P.image f := by
    exact mem_image.mpr ⟨(g.y,g.z),by simp [P];omega,by ext <;> simp [f,hx]⟩
  have he : (lowerBoxFinset g).filter FullSupport=(P.image f).erase g := by
    ext p
    simp only [mem_filter,mem_lowerBoxFinset,mem_erase]
    constructor
    · rintro ⟨⟨hle,hne⟩,hf⟩
      refine ⟨hne,mem_image.mpr ⟨(p.y,p.z),?_,?_⟩⟩
      · exact mem_product.mpr ⟨mem_Icc.mpr ⟨hf.2.1,hle.2.1⟩,
          mem_Icc.mpr ⟨hf.2.2,hle.2.2⟩⟩
      · apply Point3.ext <;> simp [f] <;> have := hle.1 <;> have := hf.1 <;> omega
    · rintro ⟨hne,hp⟩
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hp
      obtain ⟨hB,hC⟩ := mem_product.mp ha
      obtain ⟨hBl,hBu⟩ := mem_Icc.mp hB
      obtain ⟨hCl,hCu⟩ := mem_Icc.mp hC
      exact ⟨⟨⟨by simp [f,hx],hBu,hCu⟩,hne⟩,⟨by simp [f],hBl,hCl⟩⟩
  rw [he,card_erase_of_mem hgmem,card_image_of_injOn hi]
  simp [P]

/-- Literal disjoint box and three outside rows. No capacity assumption is
needed: B,C>=2 already include all x=1 core points and exclude g from the core. -/
theorem t3_unit_x_H_card_of_counts (S : CyclicStaircase) {g : Point3}
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    (fullSupportSymbolicH S g).card=g.y*g.z-1+(pair13Count S.D-2)+
      (pair13Count S.D-3)+(min (pair12Count S.D-2) (pair13Count S.D-1)-1) := by
  classical
  let r := pair12Count S.D
  let s := pair13Count S.D
  let L := min (r-2) (s-1)
  let B := (lowerBoxFinset g).filter FullSupport
  let R := xRow 2 (s-1) 1 1
  let T := xRow 2 (s-2) 1 2
  let U := xRow 2 L 2 1
  have hs : 3 ≤ s := by have := ho.1;dsimp [s];omega
  have hsr : s ≤ r := ho.2
  have he : fullSupportSymbolicH S g=((B ∪ R) ∪ T) ∪ U := by
    ext p
    simp only [fullSupportSymbolicH,mem_union,mem_puncturedFullCoreFinset,
      mem_filter,mem_lowerBoxFinset]
    have hR := mem_xRow 2 (s-1) 1 1 p
    have hT := mem_xRow 2 (s-2) 1 2 p
    have hU := mem_xRow 2 L 2 1 p
    constructor
    · rintro (⟨hc,hn⟩ | hb)
      · obtain ⟨hpx,hpy,hpz,hxy,hxz,hyz⟩ := hc
        rw [ht] at hyz
        by_cases hbox : p ≤ g
        · left;left;left
          exact mem_filter.mpr ⟨(mem_lowerBoxFinset g p).mpr
            ⟨hbox,by intro e;subst p;exact hn le_rfl⟩,⟨hpx,hpy,hpz⟩⟩
        · have hlarge : 2 ≤ p.x := by
            by_contra hn'
            apply hbox
            exact ⟨by omega,by omega,by omega⟩
          have hp : (p.y=1 ∧ p.z=1) ∨ (p.y=1 ∧ p.z=2) ∨
              (p.y=2 ∧ p.z=1) := by omega
          rcases hp with h11 | h12 | h21
          · left;left;right;apply hR.mpr;dsimp [r,s] at *;omega
          · left;right;apply hT.mpr;dsimp [r,s] at *;omega
          · right;apply hU.mpr;dsimp [L,r,s] at *;omega
      · exact Or.inl (Or.inl (Or.inl (mem_filter.mpr
          ⟨(mem_lowerBoxFinset g p).mpr hb.1,hb.2⟩)))
    · rintro (((hb | hr) | ht') | hu)
      · have h := mem_filter.mp hb
        exact Or.inr ⟨(mem_lowerBoxFinset g p).mp h.1,h.2⟩
      · left
        obtain ⟨hl,hu,hpy,hpz⟩ := hR.mp hr
        constructor
        · simp only [FullCore,ht];dsimp [r,s] at *;omega
        · intro hle;have := hle.2.1;have := hle.2.2;omega
      · left
        obtain ⟨hl,hu,hpy,hpz⟩ := hT.mp ht'
        constructor
        · simp only [FullCore,ht];dsimp [r,s] at *;omega
        · intro hle;have := hle.2.1;have := hle.2.2;omega
      · left
        obtain ⟨hl,hu,hpy,hpz⟩ := hU.mp hu
        constructor
        · simp only [FullCore,ht];dsimp [L,r,s] at *;omega
        · intro hle;have := hle.2.1;have := hle.2.2;omega
  have hBR : Disjoint B R := by
    apply disjoint_left.mpr
    intro p hb hr
    have hb := ((mem_lowerBoxFinset g p).mp (mem_filter.mp hb).1).1.1
    have hr := (mem_xRow _ _ _ _ p).mp hr
    omega
  have hBT : Disjoint (B ∪ R) T := by
    apply disjoint_left.mpr
    intro p hb ht'
    have ht' := (mem_xRow _ _ _ _ p).mp ht'
    rcases mem_union.mp hb with hb | hr
    · have hb := ((mem_lowerBoxFinset g p).mp (mem_filter.mp hb).1).1.1
      omega
    · have hr := (mem_xRow _ _ _ _ p).mp hr
      omega
  have hBU : Disjoint ((B ∪ R) ∪ T) U := by
    apply disjoint_left.mpr
    intro p hb hu
    have hu := (mem_xRow _ _ _ _ p).mp hu
    rcases mem_union.mp hb with hb | ht'
    · rcases mem_union.mp hb with hb | hr
      · have hb := ((mem_lowerBoxFinset g p).mp (mem_filter.mp hb).1).1.1
        omega
      · have hr := (mem_xRow _ _ _ _ p).mp hr
        omega
    · have ht' := (mem_xRow _ _ _ _ p).mp ht'
      omega
  have hB : B.card=g.y*g.z-1 := unit_x_box_card g hx hy hz
  have hR : R.card=s-2 := by rw [card_xRow];omega
  have hT : T.card=s-3 := by rw [card_xRow];omega
  have hU : U.card=L-1 := by rw [card_xRow];omega
  rw [he,card_union_of_disjoint hBU,card_union_of_disjoint hBT,
    card_union_of_disjoint hBR,hB,hR,hT,hU]

/-- Exact H for an actual full-support minimal complement. -/
theorem t3_unit_x_H_card (S : CyclicStaircase) {g : Point3}
    (_hg : MinimalComplement S.D g) (_hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=3) (hx : g.x=1) (hy : 2 ≤ g.y) (hz : 2 ≤ g.z) :
    (fullSupportSymbolicH S g).card=g.y*g.z-1+(pair13Count S.D-2)+
      (pair13Count S.D-3)+(min (pair12Count S.D-2) (pair13Count S.D-1)-1) :=
  t3_unit_x_H_card_of_counts S ho ht hx hy hz

end NSP3
