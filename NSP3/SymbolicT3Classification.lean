import NSP3.SymbolicT3Columns

namespace NSP3
open Finset

private theorem yz_corner_lower_y (S : CyclicStaircase) {i u v : ℕ}
    (hi : 0 < i) (hir : i ≤ pair23Count S.D)
    (hu : u < Ferrers23.cornerX S i) (hv : v ≤ Ferrers23.cornerY S i) :
    Point3.mk 0 u v∈S.D := by
  let j : Fin (pair23Count S.D):=⟨i-1,by omega⟩
  have hj : j.val+1=i:=by dsimp [j];omega
  have hx:=Ferrers23.cornerX_inner S j
  have hy:=Ferrers23.cornerY_inner S j
  rw [hj] at hx hy
  let b:=orderedPair23Boundary S j
  have hp:=b.property.1.pred2_mem b.property.2.2.1
  apply S.down_closed (b:=b.val.pred2) ?_ hp
  exact ⟨by simp [Point3.pred2,b.property.2.1],
    by change u≤b.val.y-1;change Ferrers23.cornerX S i=b.val.y at hx;omega,
    by change v≤b.val.z;change Ferrers23.cornerY S i=b.val.z at hy;omega⟩

private theorem yz_corner_lower_z (S : CyclicStaircase) {i u v : ℕ}
    (hi : 0 < i) (hir : i ≤ pair23Count S.D)
    (hu : u ≤ Ferrers23.cornerX S i) (hv : v < Ferrers23.cornerY S i) :
    Point3.mk 0 u v∈S.D := by
  let j : Fin (pair23Count S.D):=⟨i-1,by omega⟩
  have hj : j.val+1=i:=by dsimp [j];omega
  have hx:=Ferrers23.cornerX_inner S j
  have hy:=Ferrers23.cornerY_inner S j
  rw [hj] at hx hy
  let b:=orderedPair23Boundary S j
  have hp:=b.property.1.pred3_mem b.property.2.2.2
  apply S.down_closed (b:=b.val.pred3) ?_ hp
  exact ⟨by simp [Point3.pred3,b.property.2.1],
    by change u≤b.val.y;change Ferrers23.cornerX S i=b.val.y at hx;omega,
    by change v≤b.val.z-1;change Ferrers23.cornerY S i=b.val.z at hy;omega⟩

private theorem missing_yz_boundary (S : CyclicStaircase) {u v : ℕ}
    (hY : u<pure2Intercept S) (hZ : v<pure3Intercept S)
    (hnot : Point3.mk 0 u v∉S.D) :
    ∃ b : Pair23Boundary S, b.val.y≤u ∧ b.val.z≤v := by
  obtain ⟨b,hb,hle⟩:=exists_minimalComplement_le hnot
  have hx : b.x=0:=by have:=hle.1;change b.x≤0 at this;omega
  have hy : b.y≤u:=hle.2.1
  have hz : b.z≤v:=hle.2.2
  have hyp : 0<b.y := by
    by_contra hn
    have hzero : b.y=0:=by omega
    have he : Point3.mk 0 0 b.z=b:=by ext <;> simp [hx,hzero]
    exact hb.not_mem (he ▸ (pure3_axis_mem_iff S _).mpr (by omega))
  have hzp : 0<b.z := by
    by_contra hn
    have hzero : b.z=0:=by omega
    have he : Point3.mk 0 b.y 0=b:=by ext <;> simp [hx,hzero]
    exact hb.not_mem (he ▸ (pure2_axis_mem_iff S _).mpr (by omega))
  exact ⟨⟨b,hb,hx,hyp,hzp⟩,hy,hz⟩

/-- Missing13 forces three actual standards, without assuming area five. -/
theorem t3_missing13_standard_points (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hz : g.z=1)
    (hY : 5≤pure2Intercept S) (hZ : 5≤pure3Intercept S)
    (hnot : Point3.mk 0 1 3∉S.D) :
    Point3.mk 0 2 2∈S.D ∧ Point3.mk 0 3 1∈S.D ∧ Point3.mk 0 4 1∈S.D := by
  obtain ⟨b,hby,hbz⟩:=missing_yz_boundary S (by omega) (by omega) hnot
  obtain ⟨i,hi⟩:=Ferrers23.orderedPair23Boundary_exhaustive S b
  have hbase:=orderedPair23Boundary_y_baseline S i
  rw [hi] at hbase
  have hi1 : i.val+1=1:=by omega
  have hfirst:=Ferrers23.cornerY_inner S i
  rw [hi1,hi] at hfirst
  have h12:=Ferrers23.cornerY_lt S (i:=1) (j:=2) (by omega) (by omega)
  have h23:=Ferrers23.cornerY_lt S (i:=2) (j:=3) (by omega) (by omega)
  have h34:=Ferrers23.cornerY_lt S (i:=3) (j:=4) (by omega) (by omega)
  have hlast : Ferrers23.cornerY S 4=0:=by simpa [ht] using Ferrers23.cornerY_last S
  have hy1 : Ferrers23.cornerY S 1=3:=by omega
  have hy2 : Ferrers23.cornerY S 2=2:=by omega
  have hy3 : Ferrers23.cornerY S 3=1:=by omega
  have hx01:=Ferrers23.cornerX_lt S (i:=0) (j:=1) (by omega) (by omega)
  simp only [Ferrers23.cornerX_zero] at hx01
  have hgap1:=Ferrers23.high_edge_gap S hg hf (i:=1) (by simp [ht,hy,hz])
  have hgap2:=Ferrers23.high_edge_gap S hg hf (i:=2) (by simp [ht,hy,hz])
  norm_num [hy,hz,Ferrers23.gapU,Ferrers23.gapV,hy1,hy2,hy3] at hgap1 hgap2
  have hx2 : 3≤Ferrers23.cornerX S 2:=by omega
  have hx3 : 5≤Ferrers23.cornerX S 3:=by omega
  exact ⟨yz_corner_lower_y S (i:=2) (by omega) (by omega) (by omega) (by omega),
    yz_corner_lower_y S (i:=3) (by omega) (by omega) (by omega) (by omega),
    yz_corner_lower_y S (i:=3) (by omega) (by omega) (by omega) (by omega)⟩

/-- Reflected missing31 argument uses actual same-S corners, not an assumed
coordinate-permutation API. -/
theorem t3_missing31_standard_points (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=3) (hy : g.y=1) (hz : g.z=1)
    (hY : 5≤pure2Intercept S) (hZ : 5≤pure3Intercept S)
    (hnot : Point3.mk 0 3 1∉S.D) :
    Point3.mk 0 2 2∈S.D ∧ Point3.mk 0 1 3∈S.D ∧ Point3.mk 0 1 4∈S.D := by
  obtain ⟨b,hby,hbz⟩:=missing_yz_boundary S (by omega) (by omega) hnot
  obtain ⟨i,hi⟩:=Ferrers23.orderedPair23Boundary_exhaustive S b
  have hbase:=orderedPair23Boundary_z_baseline S i
  rw [hi] at hbase
  have hi3 : i.val+1=3:=by have:=i.isLt;omega
  have hlast:=Ferrers23.cornerX_inner S i
  rw [hi3,hi] at hlast
  have h01:=Ferrers23.cornerX_lt S (i:=0) (j:=1) (by omega) (by omega)
  simp only [Ferrers23.cornerX_zero] at h01
  have h12:=Ferrers23.cornerX_lt S (i:=1) (j:=2) (by omega) (by omega)
  have h23:=Ferrers23.cornerX_lt S (i:=2) (j:=3) (by omega) (by omega)
  have hx1 : Ferrers23.cornerX S 1=1:=by omega
  have hx2 : Ferrers23.cornerX S 2=2:=by omega
  have hx3 : Ferrers23.cornerX S 3=3:=by omega
  have h34:=Ferrers23.cornerY_lt S (i:=3) (j:=4) (by omega) (by omega)
  have hy4 : Ferrers23.cornerY S 4=0:=by simpa [ht] using Ferrers23.cornerY_last S
  have hgap1:=Ferrers23.high_edge_gap S hg hf (i:=1) (by simp [ht,hy,hz])
  have hgap2:=Ferrers23.high_edge_gap S hg hf (i:=2) (by simp [ht,hy,hz])
  norm_num [hy,hz,Ferrers23.gapU,Ferrers23.gapV,hx1,hx2,hx3] at hgap1 hgap2
  have hy2 : 3≤Ferrers23.cornerY S 2:=by omega
  have hy1 : 5≤Ferrers23.cornerY S 1:=by omega
  exact ⟨yz_corner_lower_z S (i:=2) (by omega) (by omega) (by omega) (by omega),
    yz_corner_lower_z S (i:=1) (by omega) (by omega) (by omega) (by omega),
    yz_corner_lower_z S (i:=1) (by omega) (by omega) (by omega) (by omega)⟩

end NSP3
