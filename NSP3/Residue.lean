import NSP3.Boundary

namespace NSP3

/-- The weighted cyclic residue of a lattice point. -/
def residueOf {m : ℕ} (p1 p2 p3 : ZMod m) (q : Point3) : ZMod m :=
  q.x * p1 + q.y * p2 + q.z * p3

/-- The genuine hypotheses of a finite cyclic-modular staircase.

The equivalence is the frozen assumption that the weighted residue map on `D` is bijective;
no return-geometry conclusion is stored here. -/
structure CyclicStaircase where
  m : ℕ
  hm : 0 < m
  D : Finset Point3
  down_closed : IsDownset D
  p1 : ZMod m
  p2 : ZMod m
  p3 : ZMod m
  residueEquiv : {q : Point3 // q ∈ D} ≃ ZMod m
  residueEquiv_spec : ∀ q, residueEquiv q = residueOf p1 p2 p3 q.1

namespace CyclicStaircase

def residue (S : CyclicStaircase) (q : Point3) : ZMod S.m :=
  residueOf S.p1 S.p2 S.p3 q

/-- The standard set has exactly `m` elements, derived from the residue equivalence. -/
theorem card_D (S : CyclicStaircase) : S.D.card = S.m := by
  let _ : NeZero S.m := ⟨Nat.ne_of_gt S.hm⟩
  calc
    S.D.card = Fintype.card {q : Point3 // q ∈ S.D} := by simp
    _ = Fintype.card (ZMod S.m) := Fintype.card_congr S.residueEquiv
    _ = S.m := ZMod.card S.m

@[simp] theorem residue_zero (S : CyclicStaircase) : S.residue Point3.zero = 0 := by
  simp [residue, residueOf, Point3.zero]

theorem residue_add (S : CyclicStaircase) (a b : Point3) :
    S.residue (a + b) = S.residue a + S.residue b := by
  simp only [residue, residueOf, Point3.add_x, Point3.add_y, Point3.add_z, Nat.cast_add]
  ring

private def rhoSubtype (S : CyclicStaircase) (b : Point3) : {q : Point3 // q ∈ S.D} :=
  S.residueEquiv.symm (S.residue b)

/-- The unique standard representative with the same residue as `b`. -/
def rho (S : CyclicStaircase) (b : Point3) : Point3 :=
  (S.rhoSubtype b).1

theorem rho_mem (S : CyclicStaircase) (b : Point3) : S.rho b ∈ S.D :=
  (S.rhoSubtype b).2

theorem residue_rho (S : CyclicStaircase) (b : Point3) :
    S.residue (S.rho b) = S.residue b := by
  change residueOf S.p1 S.p2 S.p3 (S.rhoSubtype b).1 = S.residue b
  rw [← S.residueEquiv_spec (S.rhoSubtype b)]
  exact S.residueEquiv.apply_symm_apply (S.residue b)

/-- Injectivity of residue on standard representatives. -/
theorem standard_eq_of_residue_eq (S : CyclicStaircase) {a b : Point3}
    (ha : a ∈ S.D) (hb : b ∈ S.D) (hres : S.residue a = S.residue b) : a = b := by
  have hsub : (⟨a, ha⟩ : {q : Point3 // q ∈ S.D}) = ⟨b, hb⟩ := by
    apply S.residueEquiv.injective
    calc
      S.residueEquiv ⟨a, ha⟩ = S.residue a := S.residueEquiv_spec _
      _ = S.residue b := hres
      _ = S.residueEquiv ⟨b, hb⟩ := by
        simpa only [residue] using (S.residueEquiv_spec ⟨b, hb⟩).symm
  exact congrArg Subtype.val hsub

theorem residue_pred1_eq_of_residue_eq (S : CyclicStaircase) {a b : Point3}
    (ha : 0 < a.x) (hb : 0 < b.x) (hres : S.residue a = S.residue b) :
    S.residue a.pred1 = S.residue b.pred1 := by
  have ha' : S.residue a.pred1 + S.residue Point3.e1 = S.residue a := by
    rw [← S.residue_add, Point3.pred1_add_e1 a ha]
  have hb' : S.residue b.pred1 + S.residue Point3.e1 = S.residue b := by
    rw [← S.residue_add, Point3.pred1_add_e1 b hb]
  calc
    S.residue a.pred1 = S.residue a - S.residue Point3.e1 := eq_sub_of_add_eq ha'
    _ = S.residue b - S.residue Point3.e1 := by rw [hres]
    _ = S.residue b.pred1 := (eq_sub_of_add_eq hb').symm

theorem residue_pred2_eq_of_residue_eq (S : CyclicStaircase) {a b : Point3}
    (ha : 0 < a.y) (hb : 0 < b.y) (hres : S.residue a = S.residue b) :
    S.residue a.pred2 = S.residue b.pred2 := by
  have ha' : S.residue a.pred2 + S.residue Point3.e2 = S.residue a := by
    rw [← S.residue_add, Point3.pred2_add_e2 a ha]
  have hb' : S.residue b.pred2 + S.residue Point3.e2 = S.residue b := by
    rw [← S.residue_add, Point3.pred2_add_e2 b hb]
  calc
    S.residue a.pred2 = S.residue a - S.residue Point3.e2 := eq_sub_of_add_eq ha'
    _ = S.residue b - S.residue Point3.e2 := by rw [hres]
    _ = S.residue b.pred2 := (eq_sub_of_add_eq hb').symm

theorem residue_pred3_eq_of_residue_eq (S : CyclicStaircase) {a b : Point3}
    (ha : 0 < a.z) (hb : 0 < b.z) (hres : S.residue a = S.residue b) :
    S.residue a.pred3 = S.residue b.pred3 := by
  have ha' : S.residue a.pred3 + S.residue Point3.e3 = S.residue a := by
    rw [← S.residue_add, Point3.pred3_add_e3 a ha]
  have hb' : S.residue b.pred3 + S.residue Point3.e3 = S.residue b := by
    rw [← S.residue_add, Point3.pred3_add_e3 b hb]
  calc
    S.residue a.pred3 = S.residue a - S.residue Point3.e3 := eq_sub_of_add_eq ha'
    _ = S.residue b - S.residue Point3.e3 := by rw [hres]
    _ = S.residue b.pred3 := (eq_sub_of_add_eq hb').symm

end CyclicStaircase

end NSP3
