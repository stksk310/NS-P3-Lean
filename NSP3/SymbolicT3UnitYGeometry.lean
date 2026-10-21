import NSP3.SymbolicT3UnitGeometry

namespace NSP3
open Finset

/-- Ordered terminal capacity on the unit-y face, derived from actual returns. -/
theorem t3_unit_y_capacity (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hy : g.y = 1) : pair12Count S.D + 1 ≤ g.x + g.z := by
  have h := pair12_terminal_return_capacity_ordered S hg hf ho
  omega

private def yRow (lo hi y z : ℕ) : Finset Point3 :=
  (Icc lo hi).image (fun x => Point3.mk x y z)

private theorem mem_yRow (lo hi y z : ℕ) (p : Point3) :
    p ∈ yRow lo hi y z ↔ lo ≤ p.x ∧ p.x ≤ hi ∧ p.y = y ∧ p.z = z := by
  constructor
  · intro hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    exact ⟨(mem_Icc.mp hx).1,(mem_Icc.mp hx).2,rfl,rfl⟩
  · rintro ⟨hl,hu,hy,hz⟩
    exact mem_image.mpr ⟨p.x,mem_Icc.mpr ⟨hl,hu⟩,by ext <;> simp_all⟩

private theorem card_yRow (lo hi y z : ℕ) :
    (yRow lo hi y z).card = hi + 1 - lo := by
  unfold yRow
  rw [card_image_iff.mpr (fun _ _ _ _ h => congrArg Point3.x h)]
  simp

private theorem unit_y_box_card (g : Point3) (hy : g.y = 1)
    (hx : 2 ≤ g.x) (hz : 2 ≤ g.z) :
    (by classical exact ((lowerBoxFinset g).filter FullSupport).card = g.x*g.z-1) := by
  classical
  let P := (Icc 1 g.x).product (Icc 1 g.z)
  let f : ℕ × ℕ → Point3 := fun p => Point3.mk p.1 1 p.2
  have hi : Set.InjOn f P := by
    intro a _ b _ h
    exact Prod.ext (congrArg Point3.x h) (congrArg Point3.z h)
  have hgmem : g ∈ P.image f := by
    exact mem_image.mpr ⟨(g.x,g.z),by simp [P];omega,by ext <;> simp [f,hy]⟩
  have he : (lowerBoxFinset g).filter FullSupport = (P.image f).erase g := by
    ext p
    simp only [mem_filter,mem_lowerBoxFinset,mem_erase]
    constructor
    · rintro ⟨⟨hle,hne⟩,hf⟩
      refine ⟨hne,mem_image.mpr ⟨(p.x,p.z),?_,?_⟩⟩
      · exact mem_product.mpr ⟨mem_Icc.mpr ⟨hf.1,hle.1⟩,
          mem_Icc.mpr ⟨hf.2.2,hle.2.2⟩⟩
      · apply Point3.ext <;> simp [f] <;> have := hle.2.1 <;> have := hf.2.1 <;> omega
    · rintro ⟨hne,hp⟩
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hp
      obtain ⟨hA,hC⟩ := mem_product.mp ha
      obtain ⟨hAl,hAu⟩ := mem_Icc.mp hA
      obtain ⟨hCl,hCu⟩ := mem_Icc.mp hC
      exact ⟨⟨⟨hAu,by simp [f,hy],hCu⟩,hne⟩,⟨hAl,by simp [f],hCl⟩⟩
  rw [he,card_erase_of_mem hgmem,card_image_of_injOn hi]
  simp [P]

/-- All-ordered exact H identity. Capacity makes the z=2 outside tail empty
when g.z=2; no r>s specialization or coordinate permutation is assumed. -/
theorem t3_unit_y_H_card_of_capacity (S : CyclicStaircase) {g : Point3}
    (ho : PairCountsOrdered S) (ht : pair23Count S.D = 3)
    (hy : g.y = 1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z)
    (hcap : pair12Count S.D + 1 ≤ g.x + g.z) :
    (fullSupportSymbolicH S g).card = g.x*g.z-1 +
      min (pair12Count S.D-2) (pair13Count S.D-1) +
      (pair13Count S.D-1-g.x)+(pair13Count S.D-2-g.x) := by
  classical
  let r := pair12Count S.D
  let s := pair13Count S.D
  let L := min (r-2) (s-1)
  let B := (lowerBoxFinset g).filter FullSupport
  let U := yRow 1 L 2 1
  let R := yRow (g.x+1) (s-1) 1 1
  let T := yRow (g.x+1) (s-2) 1 2
  have hs : 3 ≤ s := by have := ho.1;dsimp [s];omega
  have hsr : s ≤ r := ho.2
  have he : fullSupportSymbolicH S g = ((B ∪ U) ∪ R) ∪ T := by
    ext p
    simp only [fullSupportSymbolicH,mem_union,mem_puncturedFullCoreFinset,
      mem_filter,mem_lowerBoxFinset]
    have hU := mem_yRow 1 L 2 1 p
    have hR := mem_yRow (g.x+1) (s-1) 1 1 p
    have hT := mem_yRow (g.x+1) (s-2) 1 2 p
    constructor
    · rintro (⟨hc,hn⟩ | hb)
      · obtain ⟨hpx,hpy,hpz,hxy,hxz,hyz⟩ := hc
        rw [ht] at hyz
        by_cases hbox : p ≤ g
        · left;left;left
          exact mem_filter.mpr ⟨(mem_lowerBoxFinset g p).mpr ⟨hbox,by intro e;subst p;exact hn le_rfl⟩,
            ⟨hpx,hpy,hpz⟩⟩
        · have heq : (p.y=1 ∧ p.z=1) ∨ (p.y=1 ∧ p.z=2) ∨
              (p.y=2 ∧ p.z=1) := by omega
          rcases heq with h11 | h12 | h21
          · left;right
            apply hR.mpr
            have hlarge : g.x < p.x := by
              by_contra hn';apply hbox;exact ⟨by omega,by omega,by omega⟩
            dsimp [s] at *
            omega
          · right
            apply hT.mpr
            have hlarge : g.x < p.x := by
              by_contra hn';apply hbox;exact ⟨by omega,by omega,by omega⟩
            dsimp [s] at *
            omega
          · left;left;right
            apply hU.mpr
            dsimp [L,r,s] at *
            omega
      · exact Or.inl (Or.inl (Or.inl (mem_filter.mpr
          ⟨(mem_lowerBoxFinset g p).mpr hb.1,hb.2⟩)))
    · rintro (((hb | hu) | hr) | ht')
      · have h := mem_filter.mp hb
        exact Or.inr ⟨(mem_lowerBoxFinset g p).mp h.1,h.2⟩
      · left
        obtain ⟨hl,hu,hpy,hpz⟩ := hU.mp hu
        constructor
        · simp only [FullCore,ht]
          dsimp [L,r,s] at *
          omega
        · intro hle
          have := hle.2.2
          omega
      · left
        obtain ⟨hl,hu,hpy,hpz⟩ := hR.mp hr
        constructor
        · simp only [FullCore,ht]
          dsimp [r,s] at *
          omega
        · intro hle
          have := hle.2.2
          omega
      · left
        obtain ⟨hl,hu,hpy,hpz⟩ := hT.mp ht'
        constructor
        · simp only [FullCore,ht]
          dsimp [r,s] at *
          omega
        · intro hle
          have hz2 := hle.2.2
          dsimp [r,s] at *
          omega
  have hBU : Disjoint B U := by
    apply disjoint_left.mpr
    intro p hb hu
    have hb := ((mem_lowerBoxFinset g p).mp (mem_filter.mp hb).1).1.2.1
    have hu := (mem_yRow _ _ _ _ p).mp hu
    omega
  have hBR : Disjoint (B ∪ U) R := by
    apply disjoint_left.mpr
    intro p hb hr
    have hr := (mem_yRow _ _ _ _ p).mp hr
    rcases mem_union.mp hb with hb | hu
    · have hb := ((mem_lowerBoxFinset g p).mp (mem_filter.mp hb).1).1.1
      omega
    · have hu := (mem_yRow _ _ _ _ p).mp hu
      omega
  have hBT : Disjoint ((B ∪ U) ∪ R) T := by
    apply disjoint_left.mpr
    intro p hb ht'
    have ht' := (mem_yRow _ _ _ _ p).mp ht'
    rcases mem_union.mp hb with hb | hr
    · rcases mem_union.mp hb with hb | hu
      · have hb := ((mem_lowerBoxFinset g p).mp (mem_filter.mp hb).1).1.1
        omega
      · have hu := (mem_yRow _ _ _ _ p).mp hu
        omega
    · have hr := (mem_yRow _ _ _ _ p).mp hr
      omega
  have hB : B.card = g.x*g.z-1 := unit_y_box_card g hy hx hz
  have hU : U.card = L := by rw [card_yRow];omega
  have hR : R.card = s-1-g.x := by rw [card_yRow];omega
  have hT : T.card = s-2-g.x := by rw [card_yRow];omega
  rw [he,card_union_of_disjoint hBT,card_union_of_disjoint hBR,
    card_union_of_disjoint hBU,hB,hU,hR,hT]

/-- The identity for the actual ordered t3 full-support minimal complement. -/
theorem t3_unit_y_H_card (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hy : g.y = 1) (hx : 2 ≤ g.x) (hz : 2 ≤ g.z) :
    (fullSupportSymbolicH S g).card = g.x*g.z-1 +
      min (pair12Count S.D-2) (pair13Count S.D-1) +
      (pair13Count S.D-1-g.x)+(pair13Count S.D-2-g.x) :=
  t3_unit_y_H_card_of_capacity S ho ht hy hx hz (t3_unit_y_capacity S hg hf ho hy)

end NSP3
