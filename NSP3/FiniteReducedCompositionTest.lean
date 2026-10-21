import NSP3.FiniteReducedComposition
namespace NSP3

-- The exhaustion hypothesis must cover every normalized state and every completion.
example (hex : ReducedNoTarget) (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S) :
    fullTarget S ≤ S.m :=
  fullSupport_ordered_sharp_of_reduced_exhaustion hex S hg hf ho

end NSP3
