import NSP3.V03.NoFullUnified
import NSP3.V03.EightProfiles
import NSP3.SymbolicBWBulk

/-!
The accepted V03 proof route.  The eight exceptional profiles use the new
BF/H calculation; the complementary range uses unchanged symbolic resources.
In particular this file does not invoke the old endpoint-profile conclusions.
-/

namespace NSP3.V03

theorem fullSupport_large (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : 4 ≤ pair23Count S.D) : fullTarget S ≤ S.m := by
  by_cases hq :
      (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=6 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=7 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=6 ∧ pair13Count S.D=5 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=6 ∧ pair13Count S.D=6 ∧ pair23Count S.D=4) ∨
      (pair12Count S.D=5 ∧ pair13Count S.D=5 ∧ pair23Count S.D=5)
  · exact eight_profiles_sharp S hg hf ho hq
  rcases fullSupport_tGE4_reduced_cover S hg hf ho ht with h | h
  · exact h
  have hwidth : pair23Count S.D=4 ∨ pair23Count S.D=5 ∨ pair23Count S.D=6 := by
    rcases h.2.2 with h | h | h <;> omega
  have hbulk : ¬ ((pair23Count S.D=4 ∧ pair13Count S.D=4 ∧ pair12Count S.D≤7) ∨
      (pair23Count S.D=4 ∧ pair13Count S.D=5 ∧ pair12Count S.D≤6) ∨
      (pair23Count S.D=4 ∧ pair13Count S.D=6 ∧ pair12Count S.D=6) ∨
      (pair23Count S.D=5 ∧ pair13Count S.D=5 ∧ pair12Count S.D=5)) := by
    have hs := ho.1
    have hr := ho.2
    omega
  exact (fullSupport_smallwidth_core_bulk_BW_sharp S hg hf ho hwidth hbulk).trans
    (fullSupport_symbolic_BW_lower S hg hf ho)

theorem fullSupport_ordered (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    fullTarget S ≤ S.m := by
  by_cases ht : 4 ≤ pair23Count S.D
  · exact fullSupport_large S hg hf ho ht
  have hc : pair23Count S.D=0 ∨ pair23Count S.D=1 ∨
      pair23Count S.D=2 ∨ pair23Count S.D=3 := by omega
  rcases hc with ht | ht | ht | ht
  · exact le_of_lt (fullSupport_t0_strict S hg hf ho ht)
  · exact fullSupport_t1_ordered_symbolic_sharp S hg hf ho ht
  · exact fullSupport_t2_ordered_symbolic_sharp S hg hf ho ht
  · exact fullSupport_t3_ordered_symbolic_sharp S hg hf ho ht

end NSP3.V03
