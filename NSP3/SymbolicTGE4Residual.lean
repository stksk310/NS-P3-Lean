import NSP3.SymbolicTGE4LargeR
import NSP3.SymbolicTGE4Q444

namespace NSP3

/-- An exact remaining obligation, not a proof of the remaining disjunct. -/
theorem fullSupport_tGE4_residual_cover (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : 4 ≤ pair23Count S.D) :
    fullTarget S ≤ S.m ∨ (pair12Count S.D ≤ 17 ∧
      pair12Count S.D+6 < 2*(pair13Count S.D+pair23Count S.D) ∧
      ((pair23Count S.D=4 ∧ pair13Count S.D ≤ 8) ∨
       (pair23Count S.D=5 ∧ pair13Count S.D ≤ 6) ∨
       (pair23Count S.D=6 ∧ pair13Count S.D=6)) ∧
      ¬ (pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4)) := by
  rcases fullSupport_tGE4_reduced_cover S hg hf ho ht with h | h
  · exact Or.inl h
  by_cases he : pair12Count S.D=4 ∧ pair13Count S.D=4 ∧ pair23Count S.D=4
  · exact Or.inl (fullSupport_t4_q444_symbolic_sharp S hg hf ho he.1 he.2.1 he.2.2)
  · exact Or.inr ⟨h.1,h.2.1,h.2.2,he⟩

end NSP3
