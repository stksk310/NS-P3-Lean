import NSP3.SymbolicT3TwoUnitEndpoint
import NSP3.SymbolicT3NonunitSharp
namespace NSP3
example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (h12 : pair12Count S.D=3) (h13 : pair13Count S.D=3)
    (h23 : pair23Count S.D=3) (hx : g.x=1) (hy : g.y=3) (hz : g.z=1) :
    ∀ p ∈ t3r3ForcedPoints, Point3.mk p.y p.x p.z ∈ S.D :=
  t3_two_unit_131_points_mem S hg hf h12 h13 h23 hx hy hz
example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (h12 : pair12Count S.D=3) (h13 : pair13Count S.D=3)
    (h23 : pair23Count S.D=3) (hx : g.x=1) (hy : g.y=1) (hz : g.z=3) :
    ∀ p ∈ t3r3ForcedPoints, Point3.mk p.z p.y p.x ∈ S.D :=
  t3_two_unit_113_points_mem S hg hf h12 h13 h23 hx hy hz
example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : pair12Count S.D=3) (hx : g.x=1) (hy : g.y=3) (hz : g.z=1)
    (hm : S.m ≤ 30) : False := t3_two_unit_131_no_go S hg hf ho ht hr hx hy hz hm
example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hr : pair12Count S.D=3) (hx : g.x=1) (hy : g.y=1) (hz : g.z=3)
    (hm : S.m ≤ 30) : False := t3_two_unit_113_no_go S hg hf ho ht hr hx hy hz hm
example (S : CyclicStaircase) (g : Point3) (hg : MinimalComplement S.D g)
    (hf : FullSupport g) (ho : PairCountsOrdered S) (ht : pair23Count S.D=3)
    (hx : g.x=1) (hu : g.y=1 ∨ g.z=1) : fullTarget S ≤ S.m :=
  fullSupport_t3_two_unit_x_symbolic_sharp S hg hf ho ht hx hu
end NSP3
