import NSP3.SymbolicTGE4Q444

namespace NSP3

example (A B C : ℕ) (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hA3 : A ≤ 3) (hB3 : B ≤ 3) (hC3 : C ≤ 3) :
    8 ≤ max (ferrersPlaneDefect 4 A B) (rankCutPhi 4 A B)+
      max (ferrersPlaneDefect 4 A C) (rankCutPhi 4 A C)+
      max (ferrersPlaneDefect 4 B C) (rankCutPhi 4 B C) :=
  ferrers_weighted_four_small_triangle_lower A B C hA hB hC hA3 hB3 hC3

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (hr : pair12Count S.D=4)
    (hs : pair13Count S.D=4) (ht : pair23Count S.D=4) :
    49 ≤ fullSupportSymbolicBF S g := fullSupport_q444_BF_sharp_lower S hg hf ho hr hs ht

example (S : CyclicStaircase) {g : Point3} (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (hr : pair12Count S.D=4)
    (hs : pair13Count S.D=4) (ht : pair23Count S.D=4) :
    fullTarget S ≤ S.m := fullSupport_t4_q444_symbolic_sharp S hg hf ho hr hs ht

-- Exact equality boundary: no existence of such a staircase is asserted.
example (S : CyclicStaircase) (hr : pair12Count S.D=4) (hs : pair13Count S.D=4)
    (ht : pair23Count S.D=4) (g : Point3)
    (hshape : g=⟨4,1,1⟩ ∨ g=⟨1,4,1⟩ ∨ g=⟨1,1,4⟩) :
    fullSupportSymbolicBW S g=48 ∧ fullSupportAxisGain S g=1 ∧
      fullSupportSymbolicBF S g=49 := q444_axis_endpoint_exact S hr hs ht g hshape

end NSP3
