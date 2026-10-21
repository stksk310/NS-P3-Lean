import NSP3.SymbolicSmallwidthRows
import NSP3.SymbolicT1Sharp
import NSP3.SymbolicTGE4Q444

namespace NSP3

/-- Six disjoint positive rows; only the two rows facing the long cut change. -/
theorem fullCore_t4_card (S : CyclicStaircase) (hs : 4 ≤ pair13Count S.D)
    (hr : pair13Count S.D ≤ pair12Count S.D) (ht : pair23Count S.D=4) :
    6*pair13Count S.D = (fullCoreFinset S).card+
      (if pair12Count S.D=pair13Count S.D then 13
       else if pair12Count S.D=pair13Count S.D+1 then 11 else 10) := by
  classical
  have he : Finset.Icc 1 4 = {1,2,3,4} := by decide
  have hc := fullCore_card_eq_sum_rows S
  rw [ht] at hc
  have h11 : min (pair12Count S.D-1) (pair13Count S.D-1)=pair13Count S.D-1 :=
    min_eq_right (by omega)
  have h12 : min (pair12Count S.D-1) (pair13Count S.D-2)=pair13Count S.D-2 :=
    min_eq_right (by omega)
  have h13 : min (pair12Count S.D-1) (pair13Count S.D-3)=pair13Count S.D-3 :=
    min_eq_right (by omega)
  have h22 : min (pair12Count S.D-2) (pair13Count S.D-2)=pair13Count S.D-2 :=
    min_eq_right (by omega)
  norm_num [he,h11,h12,h13,h22] at hc
  split_ifs <;> omega

theorem fullCore_t4_linear_lower (S : CyclicStaircase) (hs : 4 ≤ pair13Count S.D)
    (hr : pair13Count S.D ≤ pair12Count S.D) (ht : pair23Count S.D=4) :
    6*pair13Count S.D ≤ (fullCoreFinset S).card+13 := by
  have h := fullCore_t4_card S hs hr ht
  split_ifs at h <;> omega

theorem fullSupport_H_t4_core_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D=4) :
    6*pair13Count S.D ≤ (fullSupportSymbolicH S g).card+14 := by
  have hc := fullCore_t4_linear_lower S (by have := ho.1; omega) ho.2 ht
  have hh := coreHole_card_le_largeHoleCap S hg hf ho
  have hp := card_fullCore_partition S g
  have hsub : (puncturedFullCoreFinset S g).card ≤ (fullSupportSymbolicH S g).card :=
    Finset.card_le_card (by intro p hp; exact Finset.mem_union.mpr (Or.inl hp))
  norm_num [ht,largeHoleCap] at hh
  omega

/-- Exact resource equality; the three natural subtractions introduce no lost units. -/
theorem fullSupportSymbolicBF_eq_weighted (S : CyclicStaircase) (g : Point3) :
    fullSupportSymbolicBF S g =
      1+max (pair12Count S.D) g.x+max (pair12Count S.D) g.y+
      max (pair12Count S.D) g.z+(fullSupportSymbolicH S g).card+
      Nat.choose (pair12Count S.D) 2+Nat.choose (pair13Count S.D) 2+
      Nat.choose (pair23Count S.D) 2+
      max (ferrersPlaneDefect (pair12Count S.D) g.x g.y) (rankCutPhi (pair12Count S.D) g.x g.y)+
      max (ferrersPlaneDefect (pair13Count S.D) g.x g.z) (rankCutPhi (pair13Count S.D) g.x g.z)+
      max (ferrersPlaneDefect (pair23Count S.D) g.y g.z) (rankCutPhi (pair23Count S.D) g.y g.z)+
      fullSupportAxisGain S g := by
  have h12 := le_max_left (ferrersPlaneDefect (pair12Count S.D) g.x g.y)
    (rankCutPhi (pair12Count S.D) g.x g.y)
  have h13 := le_max_left (ferrersPlaneDefect (pair13Count S.D) g.x g.z)
    (rankCutPhi (pair13Count S.D) g.x g.z)
  have h23 := le_max_left (ferrersPlaneDefect (pair23Count S.D) g.y g.z)
    (rankCutPhi (pair23Count S.D) g.y g.z)
  unfold fullSupportSymbolicBF fullSupportSymbolicBW
  omega

/-- H is used once, as the maximum of its box and punctured-core lower bounds. -/
theorem fullSupport_symbolic_BF_core_box_lower (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    1+3*pair12Count S.D+Nat.choose (pair12Count S.D) 2+
      Nat.choose (pair13Count S.D) 2+Nat.choose (pair23Count S.D) 2+
      max (g.x*g.y*g.z-1) ((fullCoreFinset S).card-largeHoleCap (pair23Count S.D))+
      max (ferrersPlaneDefect (pair12Count S.D) g.x g.y) (rankCutPhi (pair12Count S.D) g.x g.y)+
      max (ferrersPlaneDefect (pair13Count S.D) g.x g.z) (rankCutPhi (pair13Count S.D) g.x g.z)+
      max (ferrersPlaneDefect (pair23Count S.D) g.y g.z) (rankCutPhi (pair23Count S.D) g.y g.z)+
      fullSupportAxisGain S g ≤ fullSupportSymbolicBF S g := by
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
  rw [fullSupportSymbolicBF_eq_weighted]
  omega

end NSP3
