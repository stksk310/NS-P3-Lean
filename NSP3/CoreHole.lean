import NSP3.FullBoundaryCapacity
import NSP3.PuncturedCore
import NSP3.LowerBox

namespace NSP3

noncomputable def puncturedFullCoreFinset (S : CyclicStaircase) (g : Point3) :
    Finset Point3 := by
  classical
  exact (fullCoreFinset S).filter fun p => ¬ g ≤ p

noncomputable def coreHoleFinset (S : CyclicStaircase) (g : Point3) :
    Finset Point3 := by
  classical
  exact (fullCoreFinset S).filter fun p => g ≤ p

@[simp] theorem mem_puncturedFullCoreFinset (S : CyclicStaircase) (g p : Point3) :
    p ∈ puncturedFullCoreFinset S g ↔ FullCore S p ∧ ¬ g ≤ p := by
  classical
  simp [puncturedFullCoreFinset]

@[simp] theorem mem_coreHoleFinset (S : CyclicStaircase) (g p : Point3) :
    p ∈ coreHoleFinset S g ↔ FullCore S p ∧ g ≤ p := by
  classical
  simp [coreHoleFinset]

theorem puncturedFullCoreFinset_subset_D (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    puncturedFullCoreFinset S g ⊆ S.D := by
  intro p hp
  exact fullSupport_puncturedCore_mem S hg hfull
    ((mem_puncturedFullCoreFinset S g p).mp hp)

theorem fullSupport_of_mem_puncturedFullCoreFinset {S : CyclicStaircase} {g p : Point3}
    (hp : p ∈ puncturedFullCoreFinset S g) : FullSupport p := by
  have h := (mem_puncturedFullCoreFinset S g p).mp hp
  exact ⟨h.1.1, h.1.2.1, h.1.2.2.1⟩

theorem puncturedFullCore_ne_threePlaneSourcePoint {S : CyclicStaircase} {g p : Point3}
    (hp : p ∈ puncturedFullCoreFinset S g) (a : ThreePlaneSource S) :
    p ≠ threePlaneSourcePoint S a := by
  intro heq
  have hfull := fullSupport_of_mem_puncturedFullCoreFinset hp
  exact threePlaneSourcePoint_not_fullSupport S a (heq ▸ hfull)

theorem puncturedFullCoreFinset_disjoint_plane12Pos (S : CyclicStaircase) (g : Point3) :
    Disjoint (puncturedFullCoreFinset S g) (plane12PosFinset S) := by
  rw [Finset.disjoint_left]
  intro p hp hplane
  have hfull := fullSupport_of_mem_puncturedFullCoreFinset hp
  have hz := (mem_plane12PosFinset S p).mp hplane
  exact (Nat.ne_of_gt hfull.2.2) hz.2.2.2

theorem puncturedFullCoreFinset_disjoint_plane13Pos (S : CyclicStaircase) (g : Point3) :
    Disjoint (puncturedFullCoreFinset S g) (plane13PosFinset S) := by
  rw [Finset.disjoint_left]
  intro p hp hplane
  have hfull := fullSupport_of_mem_puncturedFullCoreFinset hp
  have hy := (mem_plane13PosFinset S p).mp hplane
  exact (Nat.ne_of_gt hfull.2.1) hy.2.2.1

theorem puncturedFullCoreFinset_disjoint_plane23Pos (S : CyclicStaircase) (g : Point3) :
    Disjoint (puncturedFullCoreFinset S g) (plane23PosFinset S) := by
  rw [Finset.disjoint_left]
  intro p hp hplane
  have hfull := fullSupport_of_mem_puncturedFullCoreFinset hp
  have hx := (mem_plane23PosFinset S p).mp hplane
  exact (Nat.ne_of_gt hfull.1) hx.2.1

theorem card_fullCore_partition (S : CyclicStaircase) (g : Point3) :
    (fullCoreFinset S).card = (puncturedFullCoreFinset S g).card +
      (coreHoleFinset S g).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := fullCoreFinset S) (p := fun p : Point3 => g ≤ p)
  simpa [puncturedFullCoreFinset, coreHoleFinset, Nat.add_comm] using h.symm

theorem coreHole_sum_lower {S : CyclicStaircase} {g p : Point3}
    (hp : p ∈ coreHoleFinset S g) :
    2 * (g.x + g.y + g.z) ≤
      pair12Count S.D + pair13Count S.D + pair23Count S.D := by
  have h := (mem_coreHoleFinset S g p).mp hp
  rcases h.1 with ⟨px, py, pz, h12, h13, h23⟩
  rcases h.2 with ⟨gx, gy, gz⟩
  omega

theorem coreHole_nonempty_pair12_add_four_le (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hne : (coreHoleFinset S g).Nonempty) :
    pair12Count S.D + 4 ≤ pair13Count S.D + pair23Count S.D := by
  obtain ⟨p, hp⟩ := hne
  have hsum := coreHole_sum_lower hp
  have hcap := pair12_terminal_return_capacity_ordered S hg hfull hord
  omega

theorem coreHoleFinset_eq_empty_of_pair23_le_three (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (ht : pair23Count S.D ≤ 3) :
    coreHoleFinset S g = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  have h := coreHole_nonempty_pair12_add_four_le S hg hfull hord hne
  have hts := hord.1
  have hsr := hord.2
  omega

theorem coreHoleFinset_eq_empty_of_gap (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S)
    (hgap : pair23Count S.D < pair12Count S.D - pair13Count S.D + 4) :
    coreHoleFinset S g = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  have h := coreHole_nonempty_pair12_add_four_le S hg hfull hord hne
  have hsr := hord.2
  omega

theorem deepestPuncture_pairCounts_eq_one (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hg111 : g = Point3.mk 1 1 1)
    (ht : 1 ≤ pair23Count S.D) :
    pair12Count S.D = 1 ∧ pair13Count S.D = 1 ∧ pair23Count S.D = 1 := by
  have h12 := pair12_terminal_return_capacity S hg hfull
  have h13 := pair13_terminal_return_capacity S hg hfull
  have h23 := pair23_terminal_return_capacity S hg hfull
  rw [hg111] at h12 h13 h23
  norm_num at h12 h13 h23
  have hts := hord.1
  have hsr := hord.2
  omega

theorem deepestPuncture_fullTarget_lt (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hg111 : g = Point3.mk 1 1 1)
    (ht : 1 ≤ pair23Count S.D) : fullTarget S < S.m := by
  have hcounts := deepestPuncture_pairCounts_eq_one S hg hfull hord hg111 ht
  have htarget : fullTarget S = 7 := by
    rcases hcounts with ⟨h12, h13, h23⟩
    simp [fullTarget, h12, h13, h23, quarterSquareCeil]
  have hboxsub := lowerBoxFinset_subset_D hg
  have hboxcard : (lowerBoxFinset g).card = 7 := by
    rw [hg111]
    simpa using card_lowerBoxFinset (Point3.mk 1 1 1)
  have hseven : 7 ≤ S.m := by
    rw [← S.card_D]
    rw [← hboxcard]
    exact Finset.card_le_card hboxsub
  by_contra hnot
  have hm : S.m = 7 := by omega
  have hDeq : lowerBoxFinset g = S.D := by
    apply Finset.eq_of_subset_of_card_le hboxsub
    rw [S.card_D, hm, hboxcard]
  have hq12 : pair12Count S.D = 1 := hcounts.1
  have hnon : (pair12Boundaries S.D).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < pair12Count S.D
    omega
  obtain ⟨b, hb⟩ := hnon
  have hbdata := mem_pair12Boundaries.mp hb
  have hp1 := hbdata.1.pred1_mem hbdata.2.1
  have hp2 := hbdata.1.pred2_mem hbdata.2.2.1
  rw [← hDeq, mem_lowerBoxFinset] at hp1 hp2
  rw [hg111] at hp1 hp2
  have hbx : b.x = 1 := by
    have := hp2.1.1
    change b.x ≤ 1 at this
    have hpos := hbdata.2.1
    omega
  have hby : b.y = 1 := by
    have := hp1.1.2.1
    change b.y ≤ 1 at this
    have hpos := hbdata.2.2.1
    omega
  have hbmem : b ∈ lowerBoxFinset g := by
    rw [mem_lowerBoxFinset, hg111]
    refine ⟨⟨by simp [hbx], by simp [hby], by simp [hbdata.2.2.2]⟩, ?_⟩
    intro heq
    have := congrArg Point3.z heq
    simp [hbdata.2.2.2] at this
  exact hbdata.1.not_mem (hDeq ▸ hbmem)

end NSP3
