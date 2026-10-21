import NSP3.FullBoundaryCapacity
import NSP3.LowerBox

namespace NSP3

/-- Public source-exact terminal interval adapter, for arbitrary high corners. -/
theorem pair12_high_return_bounds (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (b : Pair12Boundary S) (hx : g.x ≤ b.val.x) (hy : g.y ≤ b.val.y) :
    pure3Intercept S-g.z ≤ pair12ReturnCoord S b ∧
    pair12ReturnCoord S b < pure3Intercept S := by
  let p : Point3 := ⟨b.val.x-g.x, b.val.y-g.y, 0⟩
  have hp : p ∈ S.D := by
    apply S.down_closed (b := b.val.pred1) ?_ (b.property.1.pred1_mem b.property.2.1)
    exact ⟨by simp [p, Point3.pred1]; have := hf.1; omega,
      by simp [p, Point3.pred1], by simp [p, Point3.pred1, b.property.2.2.2]⟩
  let c := pair12ReturnCoord S b
  have hrho : S.rho b.val = Point3.mk 0 0 c := by
    apply Point3.ext
    · exact complementFaceReturn₁ S b.property.1 b.property.2.1
    · exact complementFaceReturn₂ S b.property.1 b.property.2.2.1
    · rfl
  have hc : c < pure3Intercept S := by
    apply (pure3_axis_mem_iff S c).mp
    rw [← hrho]
    exact S.rho_mem _
  have hresg : S.residue g = 0 := by
    rw [← S.residue_rho g, fullSupportBoundary_return_zero S hg hf]
    exact S.residue_zero
  have hsum : p+g = b.val+Point3.mk 0 0 g.z := by
    ext <;> simp [p, Nat.sub_add_cancel hx, Nat.sub_add_cancel hy, b.property.2.2.2]
  have hres : S.residue p = S.residue (Point3.mk 0 0 (c+g.z)) := by
    calc
      S.residue p = S.residue (p+g) := by rw [S.residue_add, hresg]; simp
      _ = S.residue (b.val+Point3.mk 0 0 g.z) := by rw [hsum]
      _ = S.residue b.val+S.residue (Point3.mk 0 0 g.z) := S.residue_add _ _
      _ = S.residue (Point3.mk 0 0 c)+S.residue (Point3.mk 0 0 g.z) := by
        rw [← S.residue_rho b.val, hrho]
      _ = S.residue (Point3.mk 0 0 (c+g.z)) := by rw [← S.residue_add]; rfl
  have hout : Point3.mk 0 0 (c+g.z) ∉ S.D := by
    intro hmem
    have heq := S.standard_eq_of_residue_eq hp hmem hres
    have heqz := congrArg Point3.z heq
    have := hf.2.2
    simp [p] at heqz
    omega
  have hlower : pure3Intercept S ≤ c+g.z := by
    by_contra h
    exact hout ((pure3_axis_mem_iff S _).mpr (by omega))
  exact ⟨by omega, hc⟩

private theorem box_pair12_collision (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    {d e z : ℕ} (hd : 0 < d) (hdg : d ≤ g.x)
    (heg : e ≤ g.y) (hzg : z < g.z)
    (hres : S.residue (Point3.mk d 0 0) = S.residue (Point3.mk 0 e z)) : False := by
  have hm1 : Point3.mk d 0 0 ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨hdg, Nat.zero_le _, Nat.zero_le _⟩,
      by intro h; have := congrArg Point3.y h; have := hf.2.1; simp_all⟩)
  have hm2 : Point3.mk 0 e z ∈ S.D := lowerBoxFinset_subset_D hg
    ((mem_lowerBoxFinset _ _).mpr ⟨⟨Nat.zero_le _, heg, Nat.le_of_lt hzg⟩,
      by intro h; have := congrArg Point3.x h; have := hf.1; simp_all⟩)
  have heq := S.standard_eq_of_residue_eq hm1 hm2 hres
  have hx := congrArg Point3.x heq
  simp only at hx
  omega

/-- Two arbitrary high corners cannot fit in a g.x by g.y rectangle. -/
theorem pair12_terminal_rectangle_separation (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (b c : Pair12Boundary S)
    (hbx : g.x ≤ b.val.x) (hby : g.y ≤ b.val.y)
    (hcx : g.x ≤ c.val.x) (hcy : g.y ≤ c.val.y)
    (horder : b.val.x < c.val.x) :
    g.x < c.val.x-b.val.x ∨ g.y < b.val.y-c.val.y := by
  by_contra h
  push Not at h
  have hyorder := pair12_y_lt_of_x_lt S.down_closed
    (mem_pair12Boundaries.mpr b.property) (mem_pair12Boundaries.mpr c.property) horder
  let d := c.val.x-b.val.x
  let e := b.val.y-c.val.y
  let rb := pair12ReturnCoord S b
  let rc := pair12ReturnCoord S c
  have hb := pair12_high_return_bounds S hg hf b hbx hby
  have hc := pair12_high_return_bounds S hg hf c hcx hcy
  have hbres : S.residue b.val = (rb : ZMod S.m)*S.p3 := by
    rw [← S.residue_rho b.val]
    simp [CyclicStaircase.residue, residueOf, complementFaceReturn₁ S b.property.1 b.property.2.1,
      complementFaceReturn₂ S b.property.1 b.property.2.2.1, rb, pair12ReturnCoord]
  have hcres : S.residue c.val = (rc : ZMod S.m)*S.p3 := by
    rw [← S.residue_rho c.val]
    simp [CyclicStaircase.residue, residueOf, complementFaceReturn₁ S c.property.1 c.property.2.1,
      complementFaceReturn₂ S c.property.1 c.property.2.2.1, rc, pair12ReturnCoord]
  have hdx : (d : ZMod S.m)+b.val.x=c.val.x := by
    rw [← Nat.cast_add, show d+b.val.x=c.val.x by dsimp [d]; omega]
  have hey : (e : ZMod S.m)+c.val.y=b.val.y := by
    rw [← Nat.cast_add, show e+c.val.y=b.val.y by dsimp [e]; omega]
  simp only [CyclicStaircase.residue, residueOf, b.property.2.2.2,
    c.property.2.2.2, Nat.cast_zero, zero_mul, add_zero] at hbres hcres
  by_cases hrc : rb ≤ rc
  · have hz : rc-rb < g.z := by dsimp [rb, rc] at *; omega
    have hr : ((rc-rb : ℕ) : ZMod S.m)+rb=rc := by
      rw [← Nat.cast_add, Nat.sub_add_cancel hrc]
    apply box_pair12_collision S hg hf (d := d) (e := e) (z := rc-rb)
      (by dsimp [d]; omega) h.1 h.2 hz
    simp only [CyclicStaircase.residue, residueOf, Nat.cast_zero, zero_mul, add_zero, zero_add]
    linear_combination hcres-hbres+hdx*S.p1-hey*S.p2-hr*S.p3
  · have hz : rb-rc < g.z := by dsimp [rb, rc] at *; omega
    have hr : ((rb-rc : ℕ) : ZMod S.m)+rc=rb := by
      rw [← Nat.cast_add, Nat.sub_add_cancel (by omega : rc ≤ rb)]
    have hm1 : Point3.mk d 0 (rb-rc) ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨h.1, Nat.zero_le _, Nat.le_of_lt hz⟩,
        by intro he; have := congrArg Point3.y he; have := hf.2.1; simp_all⟩)
    have hm2 : Point3.mk 0 e 0 ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨Nat.zero_le _, h.2, Nat.zero_le _⟩,
        by intro he; have := congrArg Point3.x he; have := hf.1; simp_all⟩)
    have hres : S.residue (Point3.mk d 0 (rb-rc))=S.residue (Point3.mk 0 e 0) := by
      simp only [CyclicStaircase.residue, residueOf, Nat.cast_zero, zero_mul, add_zero, zero_add]
      linear_combination hcres-hbres+hdx*S.p1-hey*S.p2+hr*S.p3
    have hx := congrArg Point3.x (S.standard_eq_of_residue_eq hm1 hm2 hres)
    simp only at hx
    dsimp [d] at hx
    omega

end NSP3
