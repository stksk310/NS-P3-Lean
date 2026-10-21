import NSP3.FullCore

namespace NSP3

/-- Exact positive yz-row; no minimality or realizability assumption is added. -/
theorem fullCore_positive_row_card (S : CyclicStaircase) (y z : ℕ)
    (hy : 0 < y) (hz : 0 < z) :
    ((fullCoreFinset S).filter (fun p => p.y=y ∧ p.z=z)).card =
      if y+z ≤ pair23Count S.D then
        min (pair12Count S.D-y) (pair13Count S.D-z) else 0 := by
  classical
  let L := if y+z ≤ pair23Count S.D then
    min (pair12Count S.D-y) (pair13Count S.D-z) else 0
  let f : ℕ → Point3 := fun x => Point3.mk x y z
  have hmem (x : ℕ) : FullCore S (f x) ↔ 1 ≤ x ∧ x ≤ L := by
    simp only [FullCore]
    dsimp [f,L]
    split_ifs <;> omega
  have hrow : (fullCoreFinset S).filter (fun p => p.y=y ∧ p.z=z) =
      (Finset.Icc 1 L).image f := by
    ext p
    constructor
    · intro hp
      rcases p with ⟨x,y',z'⟩
      obtain ⟨hc,he⟩ := Finset.mem_filter.mp hp
      dsimp at he
      obtain ⟨rfl,rfl⟩ := he
      exact Finset.mem_image.mpr ⟨x,Finset.mem_Icc.mpr
        ((hmem x).mp ((mem_fullCoreFinset S _).mp hc)),rfl⟩
    · intro hp
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_filter.mpr ⟨(mem_fullCoreFinset S _).mpr
        ((hmem x).mpr (Finset.mem_Icc.mp hx)),by simp [f]⟩
  have hinj : Function.Injective f := by
    intro a b hab
    exact congrArg Point3.x hab
  rw [hrow,Finset.card_image_of_injective _ hinj]
  simp [Nat.card_Icc,L]

/-- The eleven-point q444 core, valid in every larger pair-count region as well. -/
theorem fullCore_eleven_lower (S : CyclicStaircase) (hr : 4 ≤ pair12Count S.D)
    (hs : 4 ≤ pair13Count S.D) (ht : 4 ≤ pair23Count S.D) :
    11 ≤ (fullCoreFinset S).card := by
  classical
  let points : Finset Point3 := {⟨1,1,1⟩,⟨2,1,1⟩,⟨3,1,1⟩,
    ⟨1,2,1⟩,⟨2,2,1⟩,⟨1,3,1⟩,⟨1,1,2⟩,⟨2,1,2⟩,
    ⟨1,2,2⟩,⟨2,2,2⟩,⟨1,1,3⟩}
  have hcard : points.card=11 := by decide
  have hsub : points ⊆ fullCoreFinset S := by
    intro p hp
    simp only [points,Finset.mem_insert,Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals apply (mem_fullCoreFinset S _).mpr
    all_goals dsimp [FullCore]; omega
  rw [← hcard]
  exact Finset.card_le_card hsub

/-- Exact q444 cardinality, not just the smaller simplex subset. -/
theorem fullCore_q444_card (S : CyclicStaircase) (hr : pair12Count S.D=4)
    (hs : pair13Count S.D=4) (ht : pair23Count S.D=4) :
    (fullCoreFinset S).card=11 := by
  classical
  let points : Finset Point3 := {⟨1,1,1⟩,⟨2,1,1⟩,⟨3,1,1⟩,
    ⟨1,2,1⟩,⟨2,2,1⟩,⟨1,3,1⟩,⟨1,1,2⟩,⟨2,1,2⟩,
    ⟨1,2,2⟩,⟨2,2,2⟩,⟨1,1,3⟩}
  have hcard : points.card=11 := by decide
  have hsub : fullCoreFinset S ⊆ points := by
    intro p hp
    rcases p with ⟨x,y,z⟩
    have hc := (mem_fullCoreFinset S _).mp hp
    have hx : 1 ≤ x ∧ x ≤ 3 := by dsimp [FullCore] at hc; omega
    have hy : 1 ≤ y ∧ y ≤ 3 := by dsimp [FullCore] at hc; omega
    have hz : 1 ≤ z ∧ z ≤ 3 := by dsimp [FullCore] at hc; omega
    obtain ⟨hx,hx3⟩ := hx
    obtain ⟨hy,hy3⟩ := hy
    obtain ⟨hz,hz3⟩ := hz
    interval_cases x <;> interval_cases y <;> interval_cases z <;>
      norm_num [FullCore,hr,hs,ht] at hc <;> simp [points]
  apply le_antisymm
  · exact le_trans (Finset.card_le_card hsub) (le_of_eq hcard)
  · exact fullCore_eleven_lower S (by omega) (by omega) (by omega)

end NSP3
