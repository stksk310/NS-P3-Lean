import NSP3.SymbolicFerrersRankCut

/- The following six definitions reproduce FIRST_MISSING_THEOREM.lean exactly.
   The original standalone file is preserved byte for byte. This production
   module makes its obligations importable without changing Lake configuration. -/
namespace NSP3.SymbolicObligations

noncomputable def cornerX (S : CyclicStaircase) (i : ℕ) : ℕ :=
  if hzero : i=0 then 0 else if hi : i ≤ pair12Count S.D then
    (orderedPair12Boundary S ⟨i-1, by omega⟩).val.x else pure1Intercept S

noncomputable def cornerY (S : CyclicStaircase) (i : ℕ) : ℕ :=
  if hzero : i=0 then pure2Intercept S else if hi : i ≤ pair12Count S.D then
    (orderedPair12Boundary S ⟨i-1, by omega⟩).val.y else 0

noncomputable def gapU (S : CyclicStaircase) (i : ℕ) : ℕ :=
  cornerX S (i+1)-cornerX S i-1
noncomputable def gapV (S : CyclicStaircase) (i : ℕ) : ℕ :=
  cornerY S i-cornerY S (i+1)-1

noncomputable def pair_plane_exact_gap_card : Prop :=
  ∀ S : CyclicStaircase,
    (plane12PosFinset S).card =
      Nat.choose (pair12Count S.D) 2+
      (Finset.range (pair12Count S.D+1)).sum (fun i => (pair12Count S.D-i)*gapU S i)+
      (Finset.range (pair12Count S.D+1)).sum (fun j => j*gapV S j)+
      (Finset.range (pair12Count S.D+1)).sum (fun i =>
        ((Finset.range (pair12Count S.D+1)).filter (fun j => i ≤ j)).sum
          (fun j => gapU S i*gapV S j))

noncomputable def pair_plane_face_rank_lower : Prop :=
  ∀ (S : CyclicStaircase) (A B : ℕ), 0<A → 0<B → Point3.mk A B 0 ∈ S.D →
    Nat.choose (pair12Count S.D) 2+rankCutPhi (pair12Count S.D) A B ≤
      (plane12PosFinset S).card

theorem cornerX_agrees : cornerX = Ferrers.cornerX := rfl
theorem cornerY_agrees : cornerY = Ferrers.cornerY := rfl
theorem gapU_agrees : gapU = Ferrers.gapU := rfl
theorem gapV_agrees : gapV = Ferrers.gapV := rfl

/-- A proof term inhabiting the exact, universally quantified frozen obligation. -/
theorem pair_plane_exact_gap_card_proof : pair_plane_exact_gap_card := by
  intro S
  exact Ferrers.pair_plane_exact_gap_card S

theorem pair_plane_face_rank_lower_proof : pair_plane_face_rank_lower := by
  intro S A B hA hB hm
  exact Ferrers.pair_plane_face_rank_lower S hA hB hm

end NSP3.SymbolicObligations
