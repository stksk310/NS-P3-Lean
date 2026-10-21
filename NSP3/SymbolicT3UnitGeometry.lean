import NSP3.SymbolicThreePlaneBudget
import NSP3.FullBoundaryCapacity

namespace NSP3
open Finset

/-- Actual terminal capacity on a unit-z face, with no residue-unit assumption. -/
theorem t3_unit_z_capacity (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (hz : g.z = 1) : pair12Count S.D + 1 ≤ g.x + g.y := by
  have h := pair12_terminal_return_capacity_ordered S hg hf ho
  omega

/-- The seven exhaustive legal positive-coordinate classes; 111 is impossible. -/
theorem fullSupport_t3_unit_partition (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) :
    (2 ≤ g.x ∧ 2 ≤ g.y ∧ 2 ≤ g.z) ∨
    (2 ≤ g.x ∧ g.y = 1 ∧ g.z = 1) ∨
    (g.x = 1 ∧ 2 ≤ g.y ∧ g.z = 1) ∨
    (g.x = 1 ∧ g.y = 1 ∧ 2 ≤ g.z) ∨
    (2 ≤ g.x ∧ 2 ≤ g.y ∧ g.z = 1) ∨
    (2 ≤ g.x ∧ g.y = 1 ∧ 2 ≤ g.z) ∨
    (g.x = 1 ∧ 2 ≤ g.y ∧ 2 ≤ g.z) := by
  have hcap := pair12_terminal_return_capacity_ordered S hg hf ho
  obtain ⟨hxs,hys,hzs⟩ := hf
  obtain ⟨h23,h13⟩ := ho
  omega

private def unitRow (lo hi y z : ℕ) : Finset Point3 :=
  (Icc lo hi).image (fun x => Point3.mk x y z)

private theorem mem_unitRow (lo hi y z : ℕ) (p : Point3) :
    p ∈ unitRow lo hi y z ↔ lo ≤ p.x ∧ p.x ≤ hi ∧ p.y = y ∧ p.z = z := by
  constructor
  · intro hp
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
    exact ⟨(mem_Icc.mp hx).1,(mem_Icc.mp hx).2,rfl,rfl⟩
  · rintro ⟨hl,hu,hy,hz⟩
    exact mem_image.mpr ⟨p.x,mem_Icc.mpr ⟨hl,hu⟩,by ext <;> simp_all⟩

private theorem card_unitRow (lo hi y z : ℕ) :
    (unitRow lo hi y z).card = hi + 1 - lo := by
  unfold unitRow
  rw [card_image_iff.mpr (fun _ _ _ _ h => congrArg Point3.x h)]
  simp

private theorem unit_z_positive_box_card (g : Point3) (hz : g.z = 1)
    (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) :
    (by classical exact ((lowerBoxFinset g).filter FullSupport).card = g.x * g.y - 1) := by
  classical
  let P := (Icc 1 g.x).product (Icc 1 g.y)
  let f : ℕ × ℕ → Point3 := fun p => Point3.mk p.1 p.2 1
  have hi : Set.InjOn f P := by
    intro a _ b _ h
    exact Prod.ext (congrArg Point3.x h) (congrArg Point3.y h)
  have hgmem : g ∈ P.image f := by
    exact mem_image.mpr ⟨(g.x,g.y),by simp [P]; omega,by ext <;> simp [f,hz]⟩
  have he : (lowerBoxFinset g).filter FullSupport = (P.image f).erase g := by
    ext p
    simp only [mem_filter,mem_lowerBoxFinset,mem_erase]
    constructor
    · rintro ⟨⟨hle,hne⟩,hf⟩
      refine ⟨hne,mem_image.mpr ⟨(p.x,p.y),?_,?_⟩⟩
      · exact mem_product.mpr ⟨mem_Icc.mpr ⟨hf.1,hle.1⟩,
          mem_Icc.mpr ⟨hf.2.1,hle.2.1⟩⟩
      · apply Point3.ext <;> simp [f] <;> have := hle.2.2 <;> have := hf.2.2 <;> omega
    · rintro ⟨hne,hp⟩
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hp
      obtain ⟨hA,hB⟩ := mem_product.mp ha
      obtain ⟨hAl,hAu⟩ := mem_Icc.mp hA
      obtain ⟨hBl,hBu⟩ := mem_Icc.mp hB
      exact ⟨⟨⟨hAu,hBu,by simp [f,hz]⟩,hne⟩,⟨hAl,hBl,by simp [f]⟩⟩
  rw [he,card_erase_of_mem hgmem,card_image_of_injOn hi]
  simp [P]

/-- Exact H count from a punctured box and three disjoint outside rows.
The capacity is geometric and explicit here, not an added axiom. -/
theorem t3_unit_z_H_card_of_capacity (S : CyclicStaircase) {g : Point3}
    (ho : PairCountsOrdered S) (ht : pair23Count S.D = 3)
    (hz : g.z = 1) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y)
    (hcap : pair12Count S.D + 1 ≤ g.x + g.y) :
    (fullSupportSymbolicH S g).card =
      g.x * g.y + pair13Count S.D - 3 + (pair13Count S.D - 1 - g.x) +
        (min (pair12Count S.D - 2) (pair13Count S.D - 1) - g.x) := by
  classical
  let r := pair12Count S.D
  let s := pair13Count S.D
  let L := min (r-2) (s-1)
  let B := (lowerBoxFinset g).filter FullSupport
  let R := unitRow (g.x+1) (s-1) 1 1
  let T := unitRow 1 (s-2) 1 2
  let U := unitRow (g.x+1) L 2 1
  have hs : 3 ≤ s := by have := ho.1; dsimp [s]; omega
  have hsr : s ≤ r := ho.2
  have he : fullSupportSymbolicH S g = ((B ∪ R) ∪ T) ∪ U := by
    ext p
    simp only [fullSupportSymbolicH,mem_union,mem_puncturedFullCoreFinset,
      mem_filter,mem_lowerBoxFinset]
    have hR := mem_unitRow (g.x+1) (s-1) 1 1 p
    have hT := mem_unitRow 1 (s-2) 1 2 p
    have hU := mem_unitRow (g.x+1) L 2 1 p
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
          · left;left;right
            apply hR.mpr
            have hlarge : g.x < p.x := by
              by_contra hn';apply hbox;exact ⟨by omega,by omega,by omega⟩
            dsimp [s] at *
            omega
          · left;right
            apply hT.mpr
            dsimp [s] at *
            omega
          · right
            apply hU.mpr
            have hlarge : g.x < p.x := by
              by_contra hn';apply hbox;exact ⟨by omega,by omega,by omega⟩
            dsimp [L,r,s] at *
            omega
      · exact Or.inl (Or.inl (Or.inl (mem_filter.mpr
          ⟨(mem_lowerBoxFinset g p).mpr hb.1,hb.2⟩)))
    · rintro (((hb | hr) | ht') | hu)
      · have h := mem_filter.mp hb
        exact Or.inr ⟨(mem_lowerBoxFinset g p).mp h.1,h.2⟩
      · left
        obtain ⟨hl,hu,hpy,hpz⟩ := hR.mp hr
        constructor
        · simp only [FullCore,ht]
          dsimp [s,r] at *
          omega
        · intro hle
          have := hle.2.1
          omega
      · left
        obtain ⟨hl,hu,hpy,hpz⟩ := hT.mp ht'
        constructor
        · simp only [FullCore,ht]
          dsimp [s,r] at *
          omega
        · intro hle
          have := hle.2.1
          omega
      · left
        obtain ⟨hl,hu,hpy,hpz⟩ := hU.mp hu
        constructor
        · simp only [FullCore,ht]
          dsimp [L,r,s] at *
          omega
        · intro hle
          have := hle.1
          have := hle.2.1
          dsimp [L,r,s] at *
          omega
  have hBR : Disjoint B R := by
    apply disjoint_left.mpr
    intro p hb hr
    have hle := ((mem_lowerBoxFinset g p).mp (mem_filter.mp hb).1).1.1
    have hl := (mem_unitRow _ _ _ _ p).mp hr
    omega
  have hBT : Disjoint (B ∪ R) T := by
    apply disjoint_left.mpr
    intro p hb ht'
    have ht' := (mem_unitRow _ _ _ _ p).mp ht'
    rcases mem_union.mp hb with hb | hr
    · have hle := ((mem_lowerBoxFinset g p).mp (mem_filter.mp hb).1).1.2.2
      omega
    · have hr := (mem_unitRow _ _ _ _ p).mp hr
      omega
  have hBU : Disjoint ((B ∪ R) ∪ T) U := by
    apply disjoint_left.mpr
    intro p hb hu
    have hu := (mem_unitRow _ _ _ _ p).mp hu
    rcases mem_union.mp hb with hb | ht'
    · rcases mem_union.mp hb with hb | hr
      · have hle := ((mem_lowerBoxFinset g p).mp (mem_filter.mp hb).1).1.1
        omega
      · have hr := (mem_unitRow _ _ _ _ p).mp hr
        omega
    · have ht' := (mem_unitRow _ _ _ _ p).mp ht'
      omega
  have hB : B.card = g.x*g.y-1 := unit_z_positive_box_card g hz hx hy
  have hR : R.card = s-1-g.x := by rw [card_unitRow];omega
  have hT : T.card = s-2 := by rw [card_unitRow];omega
  have hU : U.card = L-g.x := by rw [card_unitRow];omega
  rw [he,card_union_of_disjoint hBU,card_union_of_disjoint hBT,
    card_union_of_disjoint hBR,hB,hR,hT,hU]
  have hp : 0 < g.x*g.y := Nat.mul_pos (by omega) (by omega)
  dsimp [L,r,s] at *
  omega

/-- The H identity for every actual ordered t3 minimal complement with z=1. -/
theorem t3_unit_z_H_card (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hz : g.z = 1) (hx : 2 ≤ g.x) (hy : 2 ≤ g.y) :
    (fullSupportSymbolicH S g).card =
      g.x * g.y + pair13Count S.D - 3 + (pair13Count S.D - 1 - g.x) +
        (min (pair12Count S.D - 2) (pair13Count S.D - 1) - g.x) :=
  t3_unit_z_H_card_of_capacity S ho ht hz hx hy (t3_unit_z_capacity S hg hf ho hz)

end NSP3
