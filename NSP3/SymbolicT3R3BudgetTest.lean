import NSP3.SymbolicT3R3Budget

namespace NSP3
example (S : CyclicStaircase) {g : Point3}
    (h12 : pair12Count S.D=3) (h13 : pair13Count S.D=3) (h23 : pair23Count S.D=3)
    (hx : g.x=3) (hy : g.y=1) (hz : g.z=1) : fullSupportSymbolicBW S g=27 :=
  t3_r3_h11_BW_height3 S h12 h13 h23 hx hy hz
example (S : CyclicStaircase) {g : Point3}
    (h12 : pair12Count S.D=3) (h13 : pair13Count S.D=3) (h23 : pair23Count S.D=3)
    (hx : 4 ≤ g.x) (hy : g.y=1) (hz : g.z=1) : fullSupportSymbolicBW S g=4*g.x+15 :=
  t3_r3_h11_BW_height_ge4 S h12 h13 h23 hx hy hz
example (S : CyclicStaircase) {g : Point3}
    (h12 : pair12Count S.D = 3) (h13 : pair13Count S.D = 3)
    (h23 : pair23Count S.D = 3) (hx : 3 ≤ g.x) (hy : g.y = 1) (hz : g.z = 1) :
    (fullSupportSymbolicH S g).card = g.x + 1 :=
  t3_r3_h11_H_card S h12 h13 h23 hx hy hz
example (S : CyclicStaircase) {g : Point3}
    (h12 : pair12Count S.D = 3) (h13 : pair13Count S.D = 3)
    (h23 : pair23Count S.D = 3) (hx : 3 ≤ g.x) (hy : g.y = 1) (hz : g.z = 1) :
    fullSupportSymbolicBW S g = 2*g.x + 19 + 2*max 1 (g.x-2) :=
  t3_r3_h11_BW_exact S h12 h13 h23 hx hy hz
example (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g) (ho : PairCountsOrdered S)
    (ht : pair23Count S.D = 3) (hr : pair12Count S.D = 3)
    (hx : 4 ≤ g.x) (hy : g.y = 1) (hz : g.z = 1) : fullTarget S ≤ S.m :=
  fullSupport_t3_h11_r3_height_ge4_sharp S hg hf ho ht hr hx hy hz
end NSP3
