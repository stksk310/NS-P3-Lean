import NSP3.SymbolicFerrersWeighted
import NSP3.SymbolicFerrersPlane13
import NSP3.SymbolicFerrersPlane23
import NSP3.SymbolicResources

namespace NSP3
open Finset

def ferrersW (r A B : ℕ) : ℕ :=
  (Icc A (r-B)).sum (fun i => min (A*(r-i)) (B*i))

def ferrersRectangle (r A B : ℕ) : Finset (ℕ × ℕ) :=
  ((Icc 1 A).product (Icc 1 B)).filter (fun p => r < p.1+p.2)

def ferrersPlaneDefect (r A B : ℕ) : ℕ :=
  max 1 (max (ferrersRectangle r A B).card (ferrersW r A B))

/-- The manuscript H: punctured positive core union positive punctured box. -/
noncomputable def fullSupportSymbolicH (S : CyclicStaircase) (g : Point3) : Finset Point3 := by
  classical
  exact puncturedFullCoreFinset S g ∪ (lowerBoxFinset g).filter FullSupport

theorem symbolic_H_partition (S : CyclicStaircase) (g : Point3) :
    fullSupportSymbolicH S g =
      puncturedFullCoreFinset S g ∪ lowerBoxFullOutsideCoreFinset S g := by
  classical
  ext p
  simp only [fullSupportSymbolicH,mem_union,mem_filter,mem_lowerBoxFinset,
    mem_puncturedFullCoreFinset,mem_lowerBoxFullOutsideCoreFinset]
  constructor
  · rintro (h | ⟨⟨hle,hne⟩,hf⟩)
    · exact Or.inl h
    · by_cases hc : FullCore S p
      · exact Or.inl ⟨hc,by intro hgp; exact hne (le_antisymm hle hgp)⟩
      · exact Or.inr ⟨hle,hne,hf,hc⟩
  · rintro (h | ⟨hle,hne,hf,_⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨hle,hne⟩,hf⟩

theorem symbolic_H_card (S : CyclicStaircase) (g : Point3) :
    (fullSupportSymbolicH S g).card =
      (puncturedFullCoreFinset S g).card+(lowerBoxFullOutsideCoreFinset S g).card := by
  classical
  rw [symbolic_H_partition,card_union_of_disjoint]
  apply disjoint_left.mpr
  intro p hp hl
  exact ((mem_lowerBoxFullOutsideCoreFinset S g p).mp hl).2.2.2
    ((mem_puncturedFullCoreFinset S g p).mp hp).1

noncomputable def fullSupportSymbolicBW (S : CyclicStaircase) (g : Point3) : ℕ :=
  1+max (pair12Count S.D) g.x+max (pair12Count S.D) g.y+max (pair12Count S.D) g.z+
  (fullSupportSymbolicH S g).card+
  (Nat.choose (pair12Count S.D) 2+ferrersPlaneDefect (pair12Count S.D) g.x g.y)+
  (Nat.choose (pair13Count S.D) 2+ferrersPlaneDefect (pair13Count S.D) g.x g.z)+
  (Nat.choose (pair23Count S.D) 2+ferrersPlaneDefect (pair23Count S.D) g.y g.z)

noncomputable def fullSupportSymbolicBF (S : CyclicStaircase) (g : Point3) : ℕ :=
  fullSupportSymbolicBW S g+
  (max (ferrersPlaneDefect (pair12Count S.D) g.x g.y) (rankCutPhi (pair12Count S.D) g.x g.y)-
    ferrersPlaneDefect (pair12Count S.D) g.x g.y)+
  (max (ferrersPlaneDefect (pair13Count S.D) g.x g.z) (rankCutPhi (pair13Count S.D) g.x g.z)-
    ferrersPlaneDefect (pair13Count S.D) g.x g.z)+
  (max (ferrersPlaneDefect (pair23Count S.D) g.y g.z) (rankCutPhi (pair23Count S.D) g.y g.z)-
    ferrersPlaneDefect (pair23Count S.D) g.y g.z)+fullSupportAxisGain S g

/-- A positive face always forces a strict plane gain, via W or Phi. -/
theorem ferrers_strict_gain (r A B : ℕ) (ha : 0<A) (hb : 0<B) :
    1 ≤ max (ferrersW r A B) (rankCutPhi r A B) := by
  by_cases hsum : A+B ≤ r
  · have hm : A ∈ Icc A (r-B) := mem_Icc.mpr ⟨le_rfl,by omega⟩
    have hs := single_le_sum (f := fun i => min (A*(r-i)) (B*i))
      (fun _ _ => Nat.zero_le _) hm
    have hprod : 0 < A*B := Nat.mul_pos ha hb
    have hmul := Nat.mul_le_mul_left A (show B ≤ r-A by omega)
    have hmin : 1 ≤ min (A*(r-A)) (B*A) := le_min (by nlinarith) (by nlinarith)
    exact le_trans (le_trans hmin hs) (le_max_left _ _)
  · apply le_trans ?_ (le_max_right _ _)
    apply le_rankCutPhi
    intro l hl
    by_cases hla : l < A
    · by_cases hlr : l < r
      · have hp : 0 < (r-l)*(A-l) := Nat.mul_pos (by omega) (by omega)
        unfold rankCutCost
        omega
      · have hlr' : l=r := by omega
        subst l
        have hp : 0 < (A-r)*(B+r-r) := Nat.mul_pos (by omega) (by omega)
        unfold rankCutCost
        omega
    · have hp : 0 < l*(B+l-r) := Nat.mul_pos (by omega) (by omega)
      unfold rankCutCost
      omega


theorem pair12_rectangle_extra_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    (ferrersRectangle (pair12Count S.D) g.x g.y).card ≤ (pair12ExtraFinset S).card := by
  classical
  let f : ℕ × ℕ → Point3 := fun p => Point3.mk p.1 p.2 0
  have hinj : Set.InjOn f (ferrersRectangle (pair12Count S.D) g.x g.y) := by
    intro p _ q _ h
    exact Prod.ext (congrArg Point3.x h) (congrArg Point3.y h)
  have hsub : (ferrersRectangle (pair12Count S.D) g.x g.y).image f ⊆ pair12ExtraFinset S := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    have hp' := mem_filter.mp hp
    have hA := mem_Icc.mp (mem_product.mp hp'.1).1
    have hB := mem_Icc.mp (mem_product.mp hp'.1).2
    have hd : f p ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨hA.2,hB.2,Nat.zero_le _⟩,
        by intro h; have he := congrArg Point3.z h; have := hf.2.2; simp [f] at he; omega⟩)
    exact (mem_pair12ExtraFinset S _).mpr ⟨hd,hA.1,hB.1,rfl,hp'.2⟩
  have hc := card_le_card hsub
  rw [card_image_of_injOn hinj] at hc
  exact hc

theorem pair12_symbolic_defect_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    max (ferrersPlaneDefect (pair12Count S.D) g.x g.y)
      (rankCutPhi (pair12Count S.D) g.x g.y) ≤ (pair12ExtraFinset S).card := by
  have hm : Point3.mk g.x g.y 0 ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨le_rfl,le_rfl,Nat.zero_le _⟩,
      by intro h; have he := congrArg Point3.z h; have := hf.2.2; simp at he; omega⟩)
  have hphi := Ferrers.pair_plane_face_rank_lower S hf.1 hf.2.1 hm
  have hcard := card_plane12PosFinset S
  have hP : rankCutPhi (pair12Count S.D) g.x g.y ≤ (pair12ExtraFinset S).card := by omega
  have hW := Ferrers.pair12_weighted_gap_lower S hg hf
  change ferrersW (pair12Count S.D) g.x g.y ≤ (pair12ExtraFinset S).card at hW
  have hE := pair12_rectangle_extra_lower S hg hf
  have hstrict := ferrers_strict_gain (pair12Count S.D) g.x g.y hf.1 hf.2.1
  have h1 : 1 ≤ (pair12ExtraFinset S).card := le_trans hstrict (max_le hW hP)
  exact max_le (max_le h1 (max_le hE hW)) hP

theorem pair13_rectangle_extra_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    (ferrersRectangle (pair13Count S.D) g.x g.z).card ≤ (pair13ExtraFinset S).card := by
  classical
  let f : ℕ × ℕ → Point3 := fun p => Point3.mk p.1 0 p.2
  have hinj : Set.InjOn f (ferrersRectangle (pair13Count S.D) g.x g.z) := by
    intro p _ q _ h
    exact Prod.ext (congrArg Point3.x h) (congrArg Point3.z h)
  have hsub : (ferrersRectangle (pair13Count S.D) g.x g.z).image f ⊆ pair13ExtraFinset S := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    have hp' := mem_filter.mp hp
    have hA := mem_Icc.mp (mem_product.mp hp'.1).1
    have hB := mem_Icc.mp (mem_product.mp hp'.1).2
    have hd : f p ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨hA.2,Nat.zero_le _,hB.2⟩,
        by intro h; have he := congrArg Point3.y h; have := hf.2.1; simp [f] at he; omega⟩)
    exact (mem_pair13ExtraFinset S _).mpr ⟨hd,hA.1,rfl,hB.1,hp'.2⟩
  have hc := card_le_card hsub
  rw [card_image_of_injOn hinj] at hc
  exact hc

theorem pair13_symbolic_defect_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    max (ferrersPlaneDefect (pair13Count S.D) g.x g.z)
      (rankCutPhi (pair13Count S.D) g.x g.z) ≤ (pair13ExtraFinset S).card := by
  have hm : Point3.mk g.x 0 g.z ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨le_rfl,Nat.zero_le _,le_rfl⟩,
      by intro h; have he := congrArg Point3.y h; have := hf.2.1; simp at he; omega⟩)
  have hphi := Ferrers13.pair_plane_face_rank_lower S hf.1 hf.2.2 hm
  have hcard := card_plane13PosFinset S
  have hP : rankCutPhi (pair13Count S.D) g.x g.z ≤ (pair13ExtraFinset S).card := by omega
  have hW := Ferrers13.pair13_weighted_gap_lower S hg hf
  change ferrersW (pair13Count S.D) g.x g.z ≤ (pair13ExtraFinset S).card at hW
  have hE := pair13_rectangle_extra_lower S hg hf
  have hstrict := ferrers_strict_gain (pair13Count S.D) g.x g.z hf.1 hf.2.2
  have h1 : 1 ≤ (pair13ExtraFinset S).card := le_trans hstrict (max_le hW hP)
  exact max_le (max_le h1 (max_le hE hW)) hP

theorem pair23_rectangle_extra_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    (ferrersRectangle (pair23Count S.D) g.y g.z).card ≤ (pair23ExtraFinset S).card := by
  classical
  let f : ℕ × ℕ → Point3 := fun p => Point3.mk 0 p.1 p.2
  have hinj : Set.InjOn f (ferrersRectangle (pair23Count S.D) g.y g.z) := by
    intro p _ q _ h
    exact Prod.ext (congrArg Point3.y h) (congrArg Point3.z h)
  have hsub : (ferrersRectangle (pair23Count S.D) g.y g.z).image f ⊆ pair23ExtraFinset S := by
    intro q hq
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hq
    have hp' := mem_filter.mp hp
    have hA := mem_Icc.mp (mem_product.mp hp'.1).1
    have hB := mem_Icc.mp (mem_product.mp hp'.1).2
    have hd : f p ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨Nat.zero_le _,hA.2,hB.2⟩,
        by intro h; have he := congrArg Point3.x h; have := hf.1; simp [f] at he; omega⟩)
    exact (mem_pair23ExtraFinset S _).mpr ⟨hd,rfl,hA.1,hB.1,hp'.2⟩
  have hc := card_le_card hsub
  rw [card_image_of_injOn hinj] at hc
  exact hc

theorem pair23_symbolic_defect_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    max (ferrersPlaneDefect (pair23Count S.D) g.y g.z)
      (rankCutPhi (pair23Count S.D) g.y g.z) ≤ (pair23ExtraFinset S).card := by
  have hm : Point3.mk 0 g.y g.z ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨Nat.zero_le _,le_rfl,le_rfl⟩,
      by intro h; have he := congrArg Point3.x h; have := hf.1; simp at he; omega⟩)
  have hphi := Ferrers23.pair_plane_face_rank_lower S hf.2.1 hf.2.2 hm
  have hcard := card_plane23PosFinset S
  have hP : rankCutPhi (pair23Count S.D) g.y g.z ≤ (pair23ExtraFinset S).card := by omega
  have hW := Ferrers23.pair23_weighted_gap_lower S hg hf
  change ferrersW (pair23Count S.D) g.y g.z ≤ (pair23ExtraFinset S).card at hW
  have hE := pair23_rectangle_extra_lower S hg hf
  have hstrict := ferrers_strict_gain (pair23Count S.D) g.y g.z hf.2.1 hf.2.2
  have h1 : 1 ≤ (pair23ExtraFinset S).card := le_trans hstrict (max_le hW hP)
  exact max_le (max_le h1 (max_le hE hW)) hP

theorem fullSupport_symbolic_BW_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    fullSupportSymbolicBW S g ≤ S.m := by
  have h := fullSupport_axis_resource_lower S hg hf ho
  have h12 := le_trans (le_max_left _ _) (pair12_symbolic_defect_lower S hg hf)
  have h13 := le_trans (le_max_left _ _) (pair13_symbolic_defect_lower S hg hf)
  have h23 := le_trans (le_max_left _ _) (pair23_symbolic_defect_lower S hg hf)
  unfold fullSupportSymbolicBW
  rw [symbolic_H_card]
  omega

theorem fullSupport_symbolic_BF_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    fullSupportSymbolicBF S g ≤ S.m := by
  have h := fullSupport_axis_resource_lower S hg hf ho
  have h12 := pair12_symbolic_defect_lower S hg hf
  have h13 := pair13_symbolic_defect_lower S hg hf
  have h23 := pair23_symbolic_defect_lower S hg hf
  have hle12 := le_max_left (ferrersPlaneDefect (pair12Count S.D) g.x g.y) (rankCutPhi (pair12Count S.D) g.x g.y)
  have hle13 := le_max_left (ferrersPlaneDefect (pair13Count S.D) g.x g.z) (rankCutPhi (pair13Count S.D) g.x g.z)
  have hle23 := le_max_left (ferrersPlaneDefect (pair23Count S.D) g.y g.z) (rankCutPhi (pair23Count S.D) g.y g.z)
  unfold fullSupportSymbolicBF fullSupportSymbolicBW
  rw [symbolic_H_card]
  omega

end NSP3

