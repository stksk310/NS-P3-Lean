import NSP3.SymbolicT3OrderedSharp
namespace NSP3
example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : pair23Count S.D=3) :
    fullTarget S ≤ S.m := fullSupport_t3_ordered_symbolic_sharp S hg hf ho ht
end NSP3
