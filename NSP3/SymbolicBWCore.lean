import NSP3.SymbolicSmallwidthStructure

namespace NSP3

/-- Literal positive yz-row sum, including all natural truncations. -/
def coreCardRows (r s t : ℕ) : ℕ :=
  ∑ y ∈ Finset.Icc 1 t, ∑ z ∈ Finset.Icc 1 t,
    if y+z ≤ t then min (r-y) (s-z) else 0

theorem fullCore_card_eq_coreCardRows (S : CyclicStaircase) :
    (fullCoreFinset S).card =
      coreCardRows (pair12Count S.D) (pair13Count S.D) (pair23Count S.D) :=
  fullCore_card_eq_sum_rows S

theorem fullSupportSymbolicBW_le_BF (S : CyclicStaircase) (g : Point3) :
    fullSupportSymbolicBW S g ≤ fullSupportSymbolicBF S g := by
  unfold fullSupportSymbolicBF
  omega

/-- Box and punctured core bound the SAME H; only their maximum is charged. -/
theorem fullSupport_symbolic_BW_core_box_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    1+3*pair12Count S.D+Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+Nat.choose (pair23Count S.D) 2+
      max (g.x*g.y*g.z-1) ((fullCoreFinset S).card-largeHoleCap (pair23Count S.D))+
      ferrersPlaneDefect (pair12Count S.D) g.x g.y+
      ferrersPlaneDefect (pair13Count S.D) g.x g.z+
      ferrersPlaneDefect (pair23Count S.D) g.y g.z ≤ fullSupportSymbolicBW S g := by
  have hb := symbolic_H_positive_box_lower S hf
  have hh := coreHole_card_le_largeHoleCap S hg hf ho
  have hp := card_fullCore_partition S g
  have hsub : (puncturedFullCoreFinset S g).card ≤ (fullSupportSymbolicH S g).card :=
    Finset.card_le_card (by intro p hp; exact Finset.mem_union.mpr (Or.inl hp))
  have hcore : (fullCoreFinset S).card-largeHoleCap (pair23Count S.D) ≤
      (fullSupportSymbolicH S g).card := by omega
  have hm := max_le hb hcore
  have hx := le_max_left (pair12Count S.D) g.x
  have hy := le_max_left (pair12Count S.D) g.y
  have hz := le_max_left (pair12Count S.D) g.z
  unfold fullSupportSymbolicBW
  omega

end NSP3
