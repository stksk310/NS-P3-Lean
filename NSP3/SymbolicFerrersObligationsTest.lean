import NSP3.SymbolicFerrersObligations

example : NSP3.SymbolicObligations.pair_plane_exact_gap_card :=
  NSP3.SymbolicObligations.pair_plane_exact_gap_card_proof

example : NSP3.SymbolicObligations.pair_plane_face_rank_lower :=
  NSP3.SymbolicObligations.pair_plane_face_rank_lower_proof

-- r=0 is a theorem-level endpoint, not an enumerated numerical fixture.
example (S : NSP3.CyclicStaircase) (h : NSP3.pair12Count S.D=0) :
    (NSP3.plane12PosFinset S).card =
      (NSP3.pure1Intercept S-1)*(NSP3.pure2Intercept S-1) := by
  have he := NSP3.Ferrers.pair_plane_exact_gap_card S
  simpa [h,NSP3.Ferrers.gapU,NSP3.Ferrers.gapV,NSP3.Ferrers.cornerX,
    NSP3.Ferrers.cornerY] using he

-- q=1 retains all three upper-triangular cross products that actually occur.
example (S : NSP3.CyclicStaircase) (h : NSP3.pair12Count S.D=1) :
    (NSP3.plane12PosFinset S).card = NSP3.Ferrers.gapU S 0+NSP3.Ferrers.gapV S 1+
      (NSP3.Ferrers.gapU S 0*NSP3.Ferrers.gapV S 0+
        NSP3.Ferrers.gapU S 0*NSP3.Ferrers.gapV S 1)+
      NSP3.Ferrers.gapU S 1*NSP3.Ferrers.gapV S 1 := by
  have he := NSP3.Ferrers.pair_plane_exact_gap_card S
  simp only [h] at he
  simp [Finset.sum_filter,Finset.sum_range_succ,Nat.add_assoc] at he ⊢
  exact he
