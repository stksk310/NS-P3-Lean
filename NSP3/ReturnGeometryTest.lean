import NSP3.ReturnGeometry

namespace NSP3

open CyclicStaircase

example (S : CyclicStaircase) {b : Point3} (hb : MinimalComplement S.D b)
    (h : 0 < b.x) : (S.rho b).x = 0 :=
  complementFaceReturn₁ S hb h

example (S : CyclicStaircase) {b : Point3} (hb : MinimalComplement S.D b)
    (h : 0 < b.y) : (S.rho b).y = 0 :=
  complementFaceReturn₂ S hb h

example (S : CyclicStaircase) {b : Point3} (hb : MinimalComplement S.D b)
    (h : 0 < b.z) : (S.rho b).z = 0 :=
  complementFaceReturn₃ S hb h

example (S : CyclicStaircase) {b : Point3} (hb : MinimalComplement S.D b)
    (i : Fin 3) (h : 0 < b.coord i) : (S.rho b).coord i = 0 :=
  complementFaceReturn S hb i h

example (S : CyclicStaircase) {b c : Point3}
    (hb : MinimalComplement S.D b) (hc : MinimalComplement S.D c)
    (hne : b ≠ c) (hi : SupportInter b c) : S.rho b ≠ S.rho c :=
  return_ne_of_support_inter S hb hc hne hi

example (S : CyclicStaircase) {b c : Point3}
    (hb : MinimalComplement S.D b) (hc : MinimalComplement S.D c)
    (hfb : FullSupport b) (hfc : FullSupport c) : b = c :=
  fullSupport_minimalComplement_atMostOne S hb hc hfb hfc

end NSP3
