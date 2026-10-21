import NSP3.Residue

namespace NSP3

open CyclicStaircase

/-- A positive first coordinate of a minimal-complement point forces the return onto the
opposite coordinate face. -/
theorem complementFaceReturn₁ (S : CyclicStaircase) {b : Point3}
    (hb : MinimalComplement S.D b) (hbx : 0 < b.x) : (S.rho b).x = 0 := by
  by_contra hrx
  have hrxpos : 0 < (S.rho b).x := Nat.pos_of_ne_zero hrx
  have hbpred : b.pred1 ∈ S.D := hb.pred1_mem hbx
  have hrpred : (S.rho b).pred1 ∈ S.D :=
    S.down_closed (Point3.pred1_le _) (S.rho_mem b)
  have hpredres : S.residue b.pred1 = S.residue (S.rho b).pred1 :=
    S.residue_pred1_eq_of_residue_eq hbx hrxpos (S.residue_rho b).symm
  have hpred : b.pred1 = (S.rho b).pred1 :=
    S.standard_eq_of_residue_eq hbpred hrpred hpredres
  have hbrho : b = S.rho b := by
    calc
      b = b.pred1 + Point3.e1 := (Point3.pred1_add_e1 b hbx).symm
      _ = (S.rho b).pred1 + Point3.e1 := congrArg (fun q => q + Point3.e1) hpred
      _ = S.rho b := Point3.pred1_add_e1 _ hrxpos
  exact hb.not_mem (hbrho ▸ S.rho_mem b)

theorem complementFaceReturn₂ (S : CyclicStaircase) {b : Point3}
    (hb : MinimalComplement S.D b) (hby : 0 < b.y) : (S.rho b).y = 0 := by
  by_contra hry
  have hrypos : 0 < (S.rho b).y := Nat.pos_of_ne_zero hry
  have hbpred : b.pred2 ∈ S.D := hb.pred2_mem hby
  have hrpred : (S.rho b).pred2 ∈ S.D :=
    S.down_closed (Point3.pred2_le _) (S.rho_mem b)
  have hpredres : S.residue b.pred2 = S.residue (S.rho b).pred2 :=
    S.residue_pred2_eq_of_residue_eq hby hrypos (S.residue_rho b).symm
  have hpred : b.pred2 = (S.rho b).pred2 :=
    S.standard_eq_of_residue_eq hbpred hrpred hpredres
  have hbrho : b = S.rho b := by
    calc
      b = b.pred2 + Point3.e2 := (Point3.pred2_add_e2 b hby).symm
      _ = (S.rho b).pred2 + Point3.e2 := congrArg (fun q => q + Point3.e2) hpred
      _ = S.rho b := Point3.pred2_add_e2 _ hrypos
  exact hb.not_mem (hbrho ▸ S.rho_mem b)

theorem complementFaceReturn₃ (S : CyclicStaircase) {b : Point3}
    (hb : MinimalComplement S.D b) (hbz : 0 < b.z) : (S.rho b).z = 0 := by
  by_contra hrz
  have hrzpos : 0 < (S.rho b).z := Nat.pos_of_ne_zero hrz
  have hbpred : b.pred3 ∈ S.D := hb.pred3_mem hbz
  have hrpred : (S.rho b).pred3 ∈ S.D :=
    S.down_closed (Point3.pred3_le _) (S.rho_mem b)
  have hpredres : S.residue b.pred3 = S.residue (S.rho b).pred3 :=
    S.residue_pred3_eq_of_residue_eq hbz hrzpos (S.residue_rho b).symm
  have hpred : b.pred3 = (S.rho b).pred3 :=
    S.standard_eq_of_residue_eq hbpred hrpred hpredres
  have hbrho : b = S.rho b := by
    calc
      b = b.pred3 + Point3.e3 := (Point3.pred3_add_e3 b hbz).symm
      _ = (S.rho b).pred3 + Point3.e3 := congrArg (fun q => q + Point3.e3) hpred
      _ = S.rho b := Point3.pred3_add_e3 _ hrzpos
  exact hb.not_mem (hbrho ▸ S.rho_mem b)

/-- Coordinate-uniform form of complement-face return. -/
theorem complementFaceReturn (S : CyclicStaircase) {b : Point3}
    (hb : MinimalComplement S.D b) (i : Fin 3) (hbi : 0 < b.coord i) :
    (S.rho b).coord i = 0 := by
  fin_cases i
  · simpa [Point3.coord] using complementFaceReturn₁ S hb hbi
  · simpa [Point3.coord] using complementFaceReturn₂ S hb hbi
  · simpa [Point3.coord] using complementFaceReturn₃ S hb hbi

/-- Distinct minimal-complement points with intersecting support have distinct returns. -/
theorem return_ne_of_support_inter (S : CyclicStaircase) {b c : Point3}
    (hb : MinimalComplement S.D b) (hc : MinimalComplement S.D c)
    (hbc : b ≠ c) (hi : SupportInter b c) : S.rho b ≠ S.rho c := by
  intro hrho
  have hres : S.residue b = S.residue c := by
    calc
      S.residue b = S.residue (S.rho b) := (S.residue_rho b).symm
      _ = S.residue (S.rho c) := by rw [hrho]
      _ = S.residue c := S.residue_rho c
  apply hbc
  rcases hi with hix | hiy | hiz
  · have hpredres := S.residue_pred1_eq_of_residue_eq hix.1 hix.2 hres
    have hpred := S.standard_eq_of_residue_eq (hb.pred1_mem hix.1) (hc.pred1_mem hix.2) hpredres
    calc
      b = b.pred1 + Point3.e1 := (Point3.pred1_add_e1 b hix.1).symm
      _ = c.pred1 + Point3.e1 := congrArg (fun q => q + Point3.e1) hpred
      _ = c := Point3.pred1_add_e1 c hix.2
  · have hpredres := S.residue_pred2_eq_of_residue_eq hiy.1 hiy.2 hres
    have hpred := S.standard_eq_of_residue_eq (hb.pred2_mem hiy.1) (hc.pred2_mem hiy.2) hpredres
    calc
      b = b.pred2 + Point3.e2 := (Point3.pred2_add_e2 b hiy.1).symm
      _ = c.pred2 + Point3.e2 := congrArg (fun q => q + Point3.e2) hpred
      _ = c := Point3.pred2_add_e2 c hiy.2
  · have hpredres := S.residue_pred3_eq_of_residue_eq hiz.1 hiz.2 hres
    have hpred := S.standard_eq_of_residue_eq (hb.pred3_mem hiz.1) (hc.pred3_mem hiz.2) hpredres
    calc
      b = b.pred3 + Point3.e3 := (Point3.pred3_add_e3 b hiz.1).symm
      _ = c.pred3 + Point3.e3 := congrArg (fun q => q + Point3.e3) hpred
      _ = c := Point3.pred3_add_e3 c hiz.2

/-- There is at most one full-support minimal-complement point. -/
theorem fullSupport_minimalComplement_atMostOne (S : CyclicStaircase) {b c : Point3}
    (hb : MinimalComplement S.D b) (hc : MinimalComplement S.D c)
    (hfb : FullSupport b) (hfc : FullSupport c) : b = c := by
  by_contra hbc
  have hrne : S.rho b ≠ S.rho c :=
    return_ne_of_support_inter S hb hc hbc (Or.inl ⟨hfb.1, hfc.1⟩)
  apply hrne
  apply Point3.ext
  · rw [complementFaceReturn₁ S hb hfb.1, complementFaceReturn₁ S hc hfc.1]
  · rw [complementFaceReturn₂ S hb hfb.2.1, complementFaceReturn₂ S hc hfc.2.1]
  · rw [complementFaceReturn₃ S hb hfb.2.2, complementFaceReturn₃ S hc hfc.2.2]

end NSP3
