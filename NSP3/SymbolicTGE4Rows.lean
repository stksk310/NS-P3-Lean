import NSP3.SymbolicThreePlaneBudget
import NSP3.SymbolicTGE4Core

namespace NSP3

/-- Exact, disjoint source-H row decomposition, including all five geometric cases. -/
theorem symbolic_H_row_card (S : CyclicStaircase) (g : Point3) (y z : ℕ) :
    ((fullSupportSymbolicH S g).filter (fun p => p.y=y ∧ p.z=z)).card =
      let L := if y+z ≤ pair23Count S.D then
        min (pair12Count S.D-y) (pair13Count S.D-z) else 0
      if y=0 ∨ z=0 then 0
      else if y ≤ g.y ∧ z ≤ g.z then
        if y=g.y ∧ z=g.z then g.x-1 else max g.x L
      else if g.y ≤ y ∧ g.z ≤ z then min (g.x-1) L else L := by
  classical
  let L := if y+z ≤ pair23Count S.D then
    min (pair12Count S.D-y) (pair13Count S.D-z) else 0
  let N := if y=0 ∨ z=0 then 0
    else if y ≤ g.y ∧ z ≤ g.z then
      if y=g.y ∧ z=g.z then g.x-1 else max g.x L
    else if g.y ≤ y ∧ g.z ≤ z then min (g.x-1) L else L
  let f : ℕ → Point3 := fun x => Point3.mk x y z
  have hmem (x : ℕ) : f x ∈ fullSupportSymbolicH S g ↔ 1 ≤ x ∧ x ≤ N := by
    have heq : f x=g ↔ x=g.x ∧ y=g.y ∧ z=g.z := by
      constructor
      · intro h; exact ⟨congrArg Point3.x h,congrArg Point3.y h,congrArg Point3.z h⟩
      · rintro ⟨hx,hy,hz⟩; apply Point3.ext <;> assumption
    simp only [fullSupportSymbolicH,Finset.mem_union,mem_puncturedFullCoreFinset,
      Finset.mem_filter,mem_lowerBoxFinset,FullCore,FullSupport]
    change (((0<x ∧ 0<y ∧ 0<z ∧ x+y ≤ pair12Count S.D ∧
        x+z ≤ pair13Count S.D ∧ y+z ≤ pair23Count S.D) ∧
        ¬ (g.x ≤ x ∧ g.y ≤ y ∧ g.z ≤ z)) ∨
      (((x ≤ g.x ∧ y ≤ g.y ∧ z ≤ g.z) ∧ f x ≠ g) ∧
        (0<x ∧ 0<y ∧ 0<z))) ↔ 1 ≤ x ∧ x ≤ N
    simp only [ne_eq,heq]
    dsimp [N,L]
    split_ifs <;> omega
  have hrow : (fullSupportSymbolicH S g).filter (fun p => p.y=y ∧ p.z=z) =
      (Finset.Icc 1 N).image f := by
    ext p
    constructor
    · intro hp
      rcases p with ⟨x,y',z'⟩
      obtain ⟨hc,he⟩ := Finset.mem_filter.mp hp
      dsimp at he
      obtain ⟨rfl,rfl⟩ := he
      exact Finset.mem_image.mpr ⟨x,Finset.mem_Icc.mpr ((hmem x).mp hc),rfl⟩
    · intro hp
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨(hmem x).mpr (Finset.mem_Icc.mp hx),by simp [f]⟩
  have hinj : Function.Injective f := by
    intro a b hab; exact congrArg Point3.x hab
  rw [hrow,Finset.card_image_of_injective _ hinj]
  simp [Nat.card_Icc,N,L]

/-- Any coordinate beyond its incident pair cut leaves the whole core unpunctured. -/
theorem fullCore_subset_symbolic_H_of_large_coordinate (S : CyclicStaircase) (g : Point3)
    (h : pair12Count S.D ≤ g.x ∨ pair12Count S.D ≤ g.y ∨ pair13Count S.D ≤ g.z) :
    fullCoreFinset S ⊆ fullSupportSymbolicH S g := by
  classical
  intro p hp
  have hc := (mem_fullCoreFinset S p).mp hp
  apply Finset.mem_union.mpr; left
  apply (mem_puncturedFullCoreFinset S g p).mpr
  refine ⟨hc,?_⟩
  intro hgp
  have hx := hgp.1; have hy := hgp.2.1; have hz := hgp.2.2
  dsimp [FullCore] at hc
  rcases h with h | h | h <;> omega

end NSP3
