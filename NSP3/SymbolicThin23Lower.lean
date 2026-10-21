import NSP3.SymbolicThinColumns
import NSP3.FullBoundaryCapacity

namespace NSP3
open Finset

/-- A real extra face point forces one of the two unit-step bases. -/
theorem thin23_unit_step_base (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ht : pair23Count S.D=2) (hy : g.y=1) (hz : g.z=1) :
    Point3.mk 0 1 2 ∈ thin23ColumnBases S g ∨
      Point3.mk 0 2 1 ∈ thin23ColumnBases S g := by
  classical
  have hdef := pair23_symbolic_defect_lower S hg hf
  have hpos : 0 < (pair23ExtraFinset S).card := by
    have h1 : 1 ≤ ferrersPlaneDefect (pair23Count S.D) g.y g.z := le_max_left _ _
    omega
  obtain ⟨p,hp⟩ := card_pos.mp hpos
  obtain ⟨hd,hx,hyp,hzp,hsum⟩ := (mem_pair23ExtraFinset S p).mp hp
  by_cases hzz : 2 ≤ p.z
  · left
    apply mem_filter.mpr
    refine ⟨(mem_pair23ExtraFinset S _).mpr ⟨?_,rfl,by decide,by decide,by simp [ht]⟩,?_⟩
    · exact S.down_closed ⟨by simp [hx],hyp,hzz⟩ hd
    · simp [hz]
  · right
    apply mem_filter.mpr
    refine ⟨(mem_pair23ExtraFinset S _).mpr ⟨?_,rfl,by decide,by decide,by simp [ht]⟩,?_⟩
    · apply S.down_closed (b := p) ?_ hd
      exact ⟨by simp [hx],by change 2 ≤ p.y; omega,hzp⟩
    · simp [hy]

/-- Both orientations have the required truncated height, including s=2. -/
theorem thin23_height_unit_step (S : CyclicStaircase) {g : Point3}
    (ho : PairCountsOrdered S) (hh : pair12Count S.D ≤ g.x) :
    pair13Count S.D-2 ≤ thin23ColumnHeight S g (Point3.mk 0 1 2) ∧
      pair13Count S.D-2 ≤ thin23ColumnHeight S g (Point3.mk 0 2 1) := by
  have hrs := ho.2
  simp only [thin23ColumnHeight,le_min_iff]
  constructor <;> constructor
  · omega
  · constructor <;> omega
  · omega
  · constructor <;> omega

/-- The uniform thin-plane lift is witnessed by actual standard points. -/
theorem thin23_lifted_columns_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (ho : PairCountsOrdered S) (ht : pair23Count S.D=2)
    (_hs : 2 ≤ pair13Count S.D) (hy : g.y=1) (hz : g.z=1) :
    pair13Count S.D-2 ≤ (thin23LiftedColumns S g).card := by
  classical
  have hcap := pair12_terminal_return_capacity_ordered S hg hf ho
  have hh : pair12Count S.D ≤ g.x := by omega
  have heights := thin23_height_unit_step S ho hh
  have hcol (p : Point3) (hp : p ∈ thin23ColumnBases S g)
      (hhp : pair13Count S.D-2 ≤ thin23ColumnHeight S g p) :
      pair13Count S.D-2 ≤ (thin23LiftedColumns S g).card := by
    have hsub : thin23Column S g p ⊆ thin23LiftedColumns S g :=
      fun _ hq => mem_biUnion.mpr ⟨p,hp,hq⟩
    have hc := card_le_card hsub
    rw [thin23_column_card] at hc
    exact le_trans hhp hc
  rcases thin23_unit_step_base S hg hf ht hy hz with hp | hp
  · exact hcol _ hp heights.1
  · exact hcol _ hp heights.2

end NSP3
