import NSP3.FullResidual
import NSP3.SmallTCofinal

namespace NSP3

/-- Every ordered full-support counterexample lies in the exact finite residual domain. -/
theorem fullSupport_counterexample_mem_residual (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hcounter : S.m ≤ fullTarget S) :
    FullResidualTuple.mk
      (pair12Count S.D) (pair13Count S.D) (pair23Count S.D) ∈
        fullResidualTupleFinset := by
  let r := pair12Count S.D
  let s := pair13Count S.D
  let t := pair23Count S.D
  have hM : fullM S ≤ fullTarget S := by
    have haccount := full_resource_accounting S hg hfull
    omega
  have hsq := fullDeficit_square_bound S hM
  have harith : (FullResidualTuple.mk r s t).largeStripArithmetic := by
    constructor
    · simpa [FullResidualTuple.largeStripArithmetic, fullResidualM, fullM,
        fullTarget, r, s, t] using hM
    · simpa [r, s, t] using hsq
  rw [mem_fullResidualTupleFinset]
  refine ⟨?_, ?_, ?_⟩
  · simpa [t, s] using hord.1
  · simpa [s, r] using hord.2
  · by_cases ht0 : t = 0
    · have hstrict := fullSupport_t0_strict S hg hfull hord (by simpa [t] using ht0)
      omega
    by_cases ht1 : t = 1
    · by_cases hr4 : 4 ≤ r
      · have hstrict := fullSupport_t1_cofinal_strict S hg hfull hord
          (by simpa [t] using ht1) (by simpa [r] using hr4)
        omega
      · exact Or.inl ⟨ht1, by simpa [r] using (show r ≤ 3 by omega)⟩
    by_cases ht2 : t = 2
    · by_cases hr10 : 10 ≤ r
      · have hstrict := fullSupport_t2_cofinal_strict S hg hfull hord
          (by simpa [t] using ht2) (by simpa [r] using hr10)
        omega
      · exact Or.inr (Or.inl ⟨ht2, by simpa [r] using (show r ≤ 9 by omega)⟩)
    by_cases ht3 : t = 3
    · by_cases hr16 : 16 ≤ r
      · have hstrict := fullSupport_t3_cofinal_strict S hg hfull hord
          (by simpa [t] using ht3) (by simpa [r] using hr16)
        omega
      · have hgap := fullSupport_t3_gap_le_five_of_counterexample S hg hfull hord
          (by simpa [t] using ht3) hcounter
        exact Or.inr (Or.inr (Or.inl ⟨ht3,
          by simpa [r] using (show r ≤ 15 by omega), by simpa [r, s] using hgap⟩))
    by_cases ht4 : t = 4
    · by_cases hs9 : 9 ≤ s
      · have hstrict := fullSupport_large_t_strict S hg hfull hord
          (Or.inl ⟨by simpa [t] using ht4, by simpa [s] using hs9⟩)
        omega
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht4,
          by simpa [s] using (show s ≤ 8 by omega), harith⟩)))
    by_cases ht5 : t = 5
    · by_cases hs7 : 7 ≤ s
      · have hstrict := fullSupport_large_t_strict S hg hfull hord
          (Or.inr (Or.inl ⟨by simpa [t] using ht5, by simpa [s] using hs7⟩))
        omega
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ht5,
          by simpa [s] using (show s ≤ 6 by omega), harith⟩))))
    by_cases ht6 : t = 6
    · have hs6 : 6 ≤ s := by
        have := hord.1
        dsimp [s, t] at *
        omega
      by_cases hs7 : 7 ≤ s
      · have hstrict := fullSupport_large_t_strict S hg hfull hord
          (Or.inr (Or.inr (Or.inl
            ⟨by simpa [t] using ht6, by simpa [s] using hs7⟩)))
        omega
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨ht6, by simpa [s] using (show s = 6 by omega), harith⟩))))
    · have ht7 : 7 ≤ t := by omega
      have hstrict := fullSupport_large_t_strict S hg hfull hord
        (Or.inr (Or.inr (Or.inr (by simpa [t] using ht7))))
      omega

end NSP3
