import NSP3.SymbolicThin3

namespace NSP3
open Finset

/-- A positive actual yz standard point above the 3-triangle is an actual
column base. No area-equality or unit-weight assumption is used. -/
theorem t3_balanced_column_base (S : CyclicStaircase) {g : Point3}
    (ht : pair23Count S.D=3) (hy : g.y=1) (hz : g.z=1)
    {u v : ℕ} (hu : 0<u) (hv : 0<v) (hs : 3<u+v)
    (hb : Point3.mk 0 u v ∈ S.D) :
    Point3.mk 0 u v ∈ thin23ColumnBases S g := by
  classical
  apply mem_filter.mpr
  refine ⟨(mem_pair23ExtraFinset S _).mpr ⟨hb,rfl,hu,hv,by simpa [ht]⟩,?_⟩
  change g.y<u ∨ g.z<v
  omega

/-- Equal-height columns have the exact truncated height k-max(u,v). -/
theorem t3_balanced_column_height (S : CyclicStaircase) {g : Point3}
    (he : pair12Count S.D=pair13Count S.D) (hh : g.x=pair12Count S.D)
    {u v : ℕ} (hu : 0<u) (hv : 0<v) :
    thin23ColumnHeight S g (Point3.mk 0 u v)=pair12Count S.D-max u v := by
  simp only [thin23ColumnHeight,←he,hh]
  omega

/-- Source-exact lift, including all nonempty truncated segments. -/
theorem t3_balanced_lifted_column_mem (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (he : pair12Count S.D=pair13Count S.D) (hh : g.x=pair12Count S.D)
    {u v x : ℕ} (hu : 0<u) (hv : 0<v) (hs : 3<u+v)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hz : g.z=1)
    (hb : Point3.mk 0 u v ∈ S.D) (hx : 1≤x)
    (hxu : x≤pair12Count S.D-u) (hxv : x≤pair12Count S.D-v) :
    Point3.mk x u v ∈ S.D := by
  classical
  apply thin23_lifted_columns_subset_D S hg hf
  apply mem_biUnion.mpr
  refine ⟨Point3.mk 0 u v,t3_balanced_column_base S ht hy hz hu hv hs hb,?_⟩
  apply mem_image.mpr
  refine ⟨x,mem_Icc.mpr ⟨hx,?_⟩,rfl⟩
  rw [t3_balanced_column_height S he hh hu hv]
  omega

/-- Every selected actual base contributes its whole column, exactly once.
The frozen general column theorem supplies actual D-membership and the frozen
support partition separates these points from all axes, faces and H. -/
theorem t3_balanced_extra_budget (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (he : pair12Count S.D=pair13Count S.D) (hh : g.x=pair12Count S.D)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hz : g.z=1)
    (B : Finset Point3)
    (hB : ∀ p ∈ B, p.x=0 ∧ 0<p.y ∧ 0<p.z ∧ 3<p.y+p.z ∧ p∈S.D) :
    pure1Intercept S+pure2Intercept S+pure3Intercept S-2+
      (plane12PosFinset S).card+(plane13PosFinset S).card+
      (plane23PosFinset S).card+(fullSupportSymbolicH S g).card+
      B.sum (fun p=>pair12Count S.D-max p.y p.z) ≤ S.m := by
  classical
  have hsub : B⊆thin23ColumnBases S g := by
    intro p hp
    obtain ⟨hx,hu,hv,hs,hd⟩:=hB p hp
    have hp0 : Point3.mk 0 p.y p.z=p := by ext <;> simp [hx]
    rw [←hp0]
    exact t3_balanced_column_base S ht hy hz hu hv hs (hp0.symm ▸ hd)
  have hsum:=sum_le_sum_of_subset (f:=thin23ColumnHeight S g) hsub
  have hEq : B.sum (thin23ColumnHeight S g)=
      B.sum (fun p=>pair12Count S.D-max p.y p.z) := by
    apply sum_congr rfl
    intro p hp
    obtain ⟨hx,hu,hv,_,_⟩:=hB p hp
    have hp0 : Point3.mk 0 p.y p.z=p := by ext <;> simp [hx]
    rw [←hp0]
    exact t3_balanced_column_height S he hh hu hv
  rw [hEq,←thin23_lifted_columns_card] at hsum
  have h:=thin23_disjoint_resource_lower S hg hf
  omega

end NSP3
