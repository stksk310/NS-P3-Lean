import NSP3.SymbolicFerrersWeighted
namespace NSP3.Ferrers

example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) :
    (Finset.Icc g.x (pair12Count S.D-g.y)).sum
      (fun i => min (g.x*(pair12Count S.D-i)) (g.y*i)) ≤ (pair12ExtraFinset S).card :=
  pair12_weighted_gap_lower S hg hf

end NSP3.Ferrers
