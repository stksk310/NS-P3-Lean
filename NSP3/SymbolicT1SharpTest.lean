import NSP3.SymbolicT1Sharp
namespace NSP3
example (S : CyclicStaircase) (g : Point3) (hf : FullSupport g) :
    g.x*g.y*g.z-1 ≤ (fullSupportSymbolicH S g).card := symbolic_H_positive_box_lower S hf
example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : pair23Count S.D=1) :
    fullTarget S ≤ S.m := fullSupport_t1_ordered_symbolic_sharp S hg hf ho ht
end NSP3
