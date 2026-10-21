import NSP3.SymbolicThreePlaneBudget
import NSP3.SymbolicProjection

namespace NSP3
open Finset

noncomputable def thin23ColumnHeight (S : CyclicStaircase) (g p : Point3) : ℕ :=
  min (pair12Count S.D-p.y) (min (pair13Count S.D-p.z) (g.x-1))

noncomputable def thin23ColumnBases (S : CyclicStaircase) (g : Point3) : Finset Point3 := by
  classical
  exact (pair23ExtraFinset S).filter (fun p => g.y < p.y ∨ g.z < p.z)

noncomputable def thin23Column (S : CyclicStaircase) (g p : Point3) : Finset Point3 :=
  (Icc 1 (thin23ColumnHeight S g p)).image (fun x => Point3.mk x p.y p.z)

noncomputable def thin23LiftedColumns (S : CyclicStaircase) (g : Point3) : Finset Point3 := by
  classical
  exact (thin23ColumnBases S g).biUnion (thin23Column S g)

theorem thin23_column_card (S : CyclicStaircase) (g p : Point3) :
    (thin23Column S g p).card = thin23ColumnHeight S g p := by
  rw [thin23Column,card_image_iff.mpr]
  · simp
  · intro a _ b _ h
    exact congrArg Point3.x h

theorem thin23_columns_disjoint (S : CyclicStaircase) (g : Point3) {p q : Point3}
    (hp : p ∈ thin23ColumnBases S g) (hq : q ∈ thin23ColumnBases S g) (hne : p≠q) :
    Disjoint (thin23Column S g p) (thin23Column S g q) := by
  classical
  apply disjoint_left.mpr
  intro a ha hb
  obtain ⟨x,_,hx⟩ := mem_image.mp ha
  obtain ⟨y,_,hy⟩ := mem_image.mp hb
  have he := hx.trans hy.symm
  have hp0 := (mem_pair23ExtraFinset S p).mp (mem_filter.mp hp).1
  have hq0 := (mem_pair23ExtraFinset S q).mp (mem_filter.mp hq).1
  apply hne
  apply Point3.ext
  · exact hp0.2.1.trans hq0.2.1.symm
  · simpa only using congrArg Point3.y he
  · simpa only using congrArg Point3.z he

/-- Exact count, with empty and truncated columns included. -/
theorem thin23_lifted_columns_card (S : CyclicStaircase) (g : Point3) :
    (thin23LiftedColumns S g).card =
      (thin23ColumnBases S g).sum (thin23ColumnHeight S g) := by
  classical
  rw [thin23LiftedColumns,card_biUnion]
  · exact sum_congr rfl (fun p _ => thin23_column_card S g p)
  · intro p hp q hq hne
    exact thin23_columns_disjoint S g hp hq hne

theorem thin23_lifted_columns_fullSupport (S : CyclicStaircase) (g : Point3) {p : Point3}
    (hp : p ∈ thin23LiftedColumns S g) : FullSupport p := by
  classical
  obtain ⟨b,hb,hp⟩ := mem_biUnion.mp hp
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
  have hbase := (mem_pair23ExtraFinset S b).mp (mem_filter.mp hb).1
  exact ⟨(mem_Icc.mp hx).1,hbase.2.2.1,hbase.2.2.2.1⟩

theorem thin23_lifted_columns_subset_D (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) :
    thin23LiftedColumns S g ⊆ S.D := by
  classical
  intro p hp
  have hfull := thin23_lifted_columns_fullSupport S g hp
  obtain ⟨b,hb,hp⟩ := mem_biUnion.mp hp
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
  have hx' := mem_Icc.mp hx
  have hbase := (mem_pair23ExtraFinset S b).mp (mem_filter.mp hb).1
  have hbound := (le_min_iff.mp hx'.2)
  have hbound' := le_min_iff.mp hbound.2
  apply fullSupport_actual_projection_lifting S hg hf hfull
  · exact pair12Triangle_subset S.down_closed hx'.1 hbase.2.2.1 (by
      change x+b.y ≤ pair12Count S.D
      omega)
  · exact pair13Triangle_subset S.down_closed hx'.1 hbase.2.2.2.1 (by
      change x+b.z ≤ pair13Count S.D
      omega)
  · have he : proj23 (Point3.mk x b.y b.z)=b := by ext <;> simp [hbase.2.1]
    exact he.symm ▸ hbase.1
  · intro hle
    have hxx := hle.1
    change g.x ≤ x at hxx
    have hgx := hf.1
    omega

/-- These columns are genuinely new: outside both the core and the g-box. -/
theorem thin23_lifted_columns_disjoint_H (S : CyclicStaircase) (g : Point3) :
    Disjoint (thin23LiftedColumns S g) (fullSupportSymbolicH S g) := by
  classical
  apply disjoint_left.mpr
  intro p hp hh
  obtain ⟨b,hb,hp⟩ := mem_biUnion.mp hp
  obtain ⟨x,_,rfl⟩ := mem_image.mp hp
  have hbase := (mem_pair23ExtraFinset S b).mp (mem_filter.mp hb).1
  have hout := (mem_filter.mp hb).2
  rw [fullSupportSymbolicH,mem_union] at hh
  rcases hh with hc | hl
  · have hcore := ((mem_puncturedFullCoreFinset S g _).mp hc).1
    have hsum := hcore.2.2.2.2.2
    change b.y+b.z ≤ pair23Count S.D at hsum
    have hgt := hbase.2.2.2.2
    omega
  · have hle := ((mem_lowerBoxFinset _ _).mp (mem_filter.mp hl).1).1
    change x ≤ g.x ∧ b.y ≤ g.y ∧ b.z ≤ g.z at hle
    rcases hout with hy | hz
    · have := hle.2.1; omega
    · have := hle.2.2; omega

end NSP3
