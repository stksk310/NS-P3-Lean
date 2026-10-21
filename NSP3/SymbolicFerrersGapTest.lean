import NSP3.SymbolicFerrersGap
namespace NSP3.Ferrers

-- Any weakened quantifier or omitted gap contribution breaks this contract.
example (S : CyclicStaircase) :
    (plane12PosFinset S).card = Nat.choose (pair12Count S.D) 2+
      (Finset.range (pair12Count S.D+1)).sum (fun i => (pair12Count S.D-i)*gapU S i)+
      (Finset.range (pair12Count S.D+1)).sum (fun j => j*gapV S j)+
      (Finset.range (pair12Count S.D+1)).sum (fun i =>
        ((Finset.range (pair12Count S.D+1)).filter (fun j => i ≤ j)).sum
          (fun j => gapU S i*gapV S j)) := pair_plane_exact_gap_card S

end NSP3.Ferrers
