import NSP3.SymbolicT3Balanced

namespace NSP3
open Finset

/-- Exact long-plane corners from actual area and the actual last standard row. -/
theorem t3_k4_long12_shape (S : CyclicStaircase)
    (hk : pair12Count S.D=4) (hY : pure2Intercept S=5)
    (hE : (pair12ExtraFinset S).card=1) (hrow : Point3.mk 4 1 0∈S.D) :
    Ferrers.cornerX S 1=1 ∧ Ferrers.cornerY S 1=4 ∧
    Ferrers.cornerX S 2=2 ∧ Ferrers.cornerY S 2=3 ∧
    Ferrers.cornerX S 3=3 ∧ Ferrers.cornerY S 3=2 ∧
    Ferrers.cornerX S 4=5 ∧ Ferrers.cornerY S 4=1 := by
  have hlast : Ferrers.cornerY S 5=0:=by simpa [hk] using Ferrers.cornerY_last S
  have hV:= Ferrers.gapV_prefix S (k:=5) (by omega)
  rw [hlast,hY] at hV
  norm_num [sum_range_succ] at hV
  have hy1:= Ferrers.gapV_prefix S (k:=1) (by omega)
  have hy2:= Ferrers.gapV_prefix S (k:=2) (by omega)
  have hy3:= Ferrers.gapV_prefix S (k:=3) (by omega)
  have hy4:= Ferrers.gapV_prefix S (k:=4) (by omega)
  norm_num [sum_range_succ,hY] at hy1 hy2 hy3 hy4
  have hy4' : Ferrers.cornerY S 4=1:=by omega
  have ha:= Ferrers.pair_plane_exact_gap_card S
  have hc:=card_plane12PosFinset S
  rw [hk,hE] at hc
  norm_num [Nat.choose] at hc
  rw [hk,hc] at ha
  norm_num [Nat.choose,sum_range_succ,sum_filter] at ha
  have hu0 : Ferrers.gapU S 0=0:=by omega
  have hu1 : Ferrers.gapU S 1=0:=by omega
  have hu2 : Ferrers.gapU S 2=0:=by omega
  have hx1:= Ferrers.gapU_prefix S (k:=1) (by omega)
  have hx2:= Ferrers.gapU_prefix S (k:=2) (by omega)
  have hx3:= Ferrers.gapU_prefix S (k:=3) (by omega)
  have hx4:= Ferrers.gapU_prefix S (k:=4) (by omega)
  norm_num [sum_range_succ,hu0,hu1,hu2] at hx1 hx2 hx3 hx4
  let b:=orderedPair12Boundary S (⟨3,by omega⟩ : Fin (pair12Count S.D))
  have hbx : Ferrers.cornerX S 4=b.val.x:=by
    simpa [b] using Ferrers.cornerX_inner S (⟨3,by omega⟩ : Fin (pair12Count S.D))
  have hby : Ferrers.cornerY S 4=b.val.y:=by
    simpa [b] using Ferrers.cornerY_inner S (⟨3,by omega⟩ : Fin (pair12Count S.D))
  have hx4' : 5≤Ferrers.cornerX S 4:=by
    by_contra hn
    have hle : b.val≤Point3.mk 4 1 0:=
      ⟨by change b.val.x≤4;omega,by change b.val.y≤1;omega,by simp [b.property.2.2.2]⟩
    exact b.property.1.not_mem (S.down_closed hle hrow)
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,hy4'⟩

/-- Exact long-plane corners from actual area and the actual last standard row. -/
theorem t3_k4_long13_shape (S : CyclicStaircase)
    (hk : pair13Count S.D=4) (hY : pure3Intercept S=5)
    (hE : (pair13ExtraFinset S).card=1) (hrow : Point3.mk 4 0 1∈S.D) :
    Ferrers13.cornerX S 1=1 ∧ Ferrers13.cornerY S 1=4 ∧
    Ferrers13.cornerX S 2=2 ∧ Ferrers13.cornerY S 2=3 ∧
    Ferrers13.cornerX S 3=3 ∧ Ferrers13.cornerY S 3=2 ∧
    Ferrers13.cornerX S 4=5 ∧ Ferrers13.cornerY S 4=1 := by
  have hlast : Ferrers13.cornerY S 5=0:=by simpa [hk] using Ferrers13.cornerY_last S
  have hV:= Ferrers13.gapV_prefix S (k:=5) (by omega)
  rw [hlast,hY] at hV
  norm_num [sum_range_succ] at hV
  have hy1:= Ferrers13.gapV_prefix S (k:=1) (by omega)
  have hy2:= Ferrers13.gapV_prefix S (k:=2) (by omega)
  have hy3:= Ferrers13.gapV_prefix S (k:=3) (by omega)
  have hy4:= Ferrers13.gapV_prefix S (k:=4) (by omega)
  norm_num [sum_range_succ,hY] at hy1 hy2 hy3 hy4
  have hy4' : Ferrers13.cornerY S 4=1:=by omega
  have ha:= Ferrers13.pair_plane_exact_gap_card S
  have hc:=card_plane13PosFinset S
  rw [hk,hE] at hc
  norm_num [Nat.choose] at hc
  rw [hk,hc] at ha
  norm_num [Nat.choose,sum_range_succ,sum_filter] at ha
  have hu0 : Ferrers13.gapU S 0=0:=by omega
  have hu1 : Ferrers13.gapU S 1=0:=by omega
  have hu2 : Ferrers13.gapU S 2=0:=by omega
  have hx1:= Ferrers13.gapU_prefix S (k:=1) (by omega)
  have hx2:= Ferrers13.gapU_prefix S (k:=2) (by omega)
  have hx3:= Ferrers13.gapU_prefix S (k:=3) (by omega)
  have hx4:= Ferrers13.gapU_prefix S (k:=4) (by omega)
  norm_num [sum_range_succ,hu0,hu1,hu2] at hx1 hx2 hx3 hx4
  let b:=orderedPair13Boundary S (⟨3,by omega⟩ : Fin (pair13Count S.D))
  have hbx : Ferrers13.cornerX S 4=b.val.x:=by
    simpa [b] using Ferrers13.cornerX_inner S (⟨3,by omega⟩ : Fin (pair13Count S.D))
  have hby : Ferrers13.cornerY S 4=b.val.z:=by
    simpa [b] using Ferrers13.cornerY_inner S (⟨3,by omega⟩ : Fin (pair13Count S.D))
  have hx4' : 5≤Ferrers13.cornerX S 4:=by
    by_contra hn
    have hle : b.val≤Point3.mk 4 0 1:=
      ⟨by change b.val.x≤4;omega,by simp [b.property.2.2.1],by change b.val.z≤1;omega⟩
    exact b.property.1.not_mem (S.down_closed hle hrow)
  exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,hy4'⟩

/-- In the saturated endpoint the actual full-support section has exactly nine points.
The lower bound is H plus two actual disjoint columns; the upper bound uses the
support partition of D, not an enumerated staircase. -/
theorem t3_balanced_k4_full_support_card (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (he : pair12Count S.D=pair13Count S.D)
    (hk : pair12Count S.D=4) (hh : g.x=4) (hy : g.y=1) (hz : g.z=1)
    (h13 : Point3.mk 0 1 3∈S.D) (h31 : Point3.mk 0 3 1∈S.D)
    (hm : S.m≤42) : (S.D.filter fun p=>0<p.x ∧ 0<p.y ∧ 0<p.z).card=9 := by
  classical
  let F:=S.D.filter (fun p=>0<p.x ∧ 0<p.y ∧ 0<p.z)
  obtain ⟨hm42,hX,hY,hZ,hE12,hE13,hA⟩:=
    t3_balanced_k4_saturation S hg hf ht he hk hh hy hz h13 h31 hm
  have hupper:=support_resources_card_lower S F (filter_subset _ _) (by
    intro p hp;exact (mem_filter.mp hp).2)
  rw [hX,hY,hZ,card_plane12PosFinset,card_plane13PosFinset,hk,←he,hk,hE12,hE13,hA] at hupper
  norm_num [Nat.choose] at hupper
  have hH:=t3_equal_height_H_lower S (g:=g) ht he (by omega) (by omega)
  have hcols : 2≤(thin23LiftedColumns S g).card := by
    have hB : ({Point3.mk 0 1 3,Point3.mk 0 3 1}:Finset Point3)⊆thin23ColumnBases S g:=by
      intro p hp
      simp only [mem_insert,mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact t3_balanced_column_base S ht hy hz (by decide) (by decide) (by decide) h13
      · exact t3_balanced_column_base S ht hy hz (by decide) (by decide) (by decide) h31
    have hs:=sum_le_sum_of_subset (f:=thin23ColumnHeight S g) hB
    have h1:=t3_balanced_column_height S (g:=g) he (by omega)
      (u:=1) (v:=3) (by decide) (by decide)
    have h3:=t3_balanced_column_height S (g:=g) he (by omega)
      (u:=3) (v:=1) (by decide) (by decide)
    rw [thin23_lifted_columns_card]
    norm_num [h1,h3,hk] at hs
    exact hs
  have hsub : fullSupportSymbolicH S g ∪ thin23LiftedColumns S g⊆F := by
    intro p hp
    apply mem_filter.mpr
    rcases mem_union.mp hp with hp | hp
    · rcases mem_union.mp hp with hc | hb
      · exact ⟨puncturedFullCoreFinset_subset_D S hg hf hc,
          fullSupport_of_mem_puncturedFullCoreFinset hc⟩
      · exact ⟨lowerBoxFinset_subset_D hg (mem_filter.mp hb).1,(mem_filter.mp hb).2⟩
    · exact ⟨thin23_lifted_columns_subset_D S hg hf hp,
        thin23_lifted_columns_fullSupport S g hp⟩
  have hlower:=card_le_card hsub
  rw [card_union_of_disjoint (thin23_lifted_columns_disjoint_H S g).symm] at hlower
  dsimp [F] at *
  omega

/-- Area-five rigidity is invoked only after the actual saturation theorem. -/
theorem t3_balanced_k4_yz_shape (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (he : pair12Count S.D=pair13Count S.D)
    (hk : pair12Count S.D=4) (hh : g.x=4) (hy : g.y=1) (hz : g.z=1)
    (h13 : Point3.mk 0 1 3∈S.D) (h31 : Point3.mk 0 3 1∈S.D)
    (hm : S.m≤42) :
    Ferrers23.cornerX S 1=1 ∧ Ferrers23.cornerY S 1=4 ∧
    Ferrers23.cornerX S 2=2 ∧ Ferrers23.cornerY S 2=2 ∧
    Ferrers23.cornerX S 3=4 ∧ Ferrers23.cornerY S 3=1 := by
  have hA:=(t3_balanced_k4_saturation S hg hf ht he hk hh hy hz h13 h31 hm).2.2.2.2.2.2
  exact thin23_three_corner_minimal_shape S hg hf ht hy hz hA

end NSP3

