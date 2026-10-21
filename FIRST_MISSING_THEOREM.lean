import NSP3.OrderedPairBoundaries
import NSP3.SymbolicFerrersRank

/- Type declarations only. These definitions name obligations; they prove nothing.
   One-based manuscript gaps use zero-based Lean i: u[i]=alpha[i+1]-1. -/
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

/-- FIRST missing primitive: actual ordered Ferrers positive-area expansion. -/
noncomputable def pair_plane_exact_gap_card : Prop :=
  ∀ S : CyclicStaircase,
    (plane12PosFinset S).card =
      Nat.choose (pair12Count S.D) 2+
      (Finset.range (pair12Count S.D+1)).sum (fun i => (pair12Count S.D-i)*gapU S i)+
      (Finset.range (pair12Count S.D+1)).sum (fun j => j*gapV S j)+
      (Finset.range (pair12Count S.D+1)).sum (fun i =>
        ((Finset.range (pair12Count S.D+1)).filter (fun j => i ≤ j)).sum
          (fun j => gapU S i*gapV S j))

/-- Dependent goal, not yet obtained from the primitive expansion/rank cut. -/
noncomputable def pair_plane_face_rank_lower : Prop :=
  ∀ (S : CyclicStaircase) (A B : ℕ), 0<A → 0<B → Point3.mk A B 0 ∈ S.D →
    Nat.choose (pair12Count S.D) 2+rankCutPhi (pair12Count S.D) A B ≤
      (plane12PosFinset S).card

end NSP3.SymbolicObligations
