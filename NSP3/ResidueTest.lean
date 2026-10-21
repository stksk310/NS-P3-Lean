import NSP3.Residue

namespace NSP3

open CyclicStaircase

example (S : CyclicStaircase) : S.D.card = S.m :=
  S.card_D

example (S : CyclicStaircase) (b : Point3) : S.rho b ∈ S.D :=
  S.rho_mem b

example (S : CyclicStaircase) (b : Point3) : S.residue (S.rho b) = S.residue b :=
  S.residue_rho b

example (S : CyclicStaircase) {a b : Point3} (ha : a ∈ S.D) (hb : b ∈ S.D)
    (hres : S.residue a = S.residue b) : a = b :=
  S.standard_eq_of_residue_eq ha hb hres

example (S : CyclicStaircase) {a b : Point3} (ha : 0 < a.x) (hb : 0 < b.x)
    (hres : S.residue a = S.residue b) :
    S.residue a.pred1 = S.residue b.pred1 :=
  S.residue_pred1_eq_of_residue_eq ha hb hres

example (S : CyclicStaircase) {a b : Point3} (ha : 0 < a.y) (hb : 0 < b.y)
    (hres : S.residue a = S.residue b) :
    S.residue a.pred2 = S.residue b.pred2 :=
  S.residue_pred2_eq_of_residue_eq ha hb hres

example (S : CyclicStaircase) {a b : Point3} (ha : 0 < a.z) (hb : 0 < b.z)
    (hres : S.residue a = S.residue b) :
    S.residue a.pred3 = S.residue b.pred3 :=
  S.residue_pred3_eq_of_residue_eq ha hb hres

end NSP3
