import NSP3.SymbolicTerminalRectangle

namespace NSP3

/-- Actual terminal return interval, without unit-weight assumptions. -/
theorem pair13_high_return_bounds (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (b : Pair13Boundary S) (ha : g.x ≤ b.val.x) (hb : g.z ≤ b.val.z) :
    pure2Intercept S-g.y ≤ pair13ReturnCoord S b ∧
    pair13ReturnCoord S b < pure2Intercept S := by
  let p := Point3.mk (b.val.x-g.x) 0 (b.val.z-g.z)
  have hp : p ∈ S.D := by
    apply S.down_closed (b := b.val.pred1) ?_ (b.property.1.pred1_mem b.property.2.1)
    exact ⟨by simp [p, Point3.pred1]; have := hf.1; omega,by simp [p, Point3.pred1, b.property.2.2.1],by simp [p, Point3.pred1]⟩
  let r := pair13ReturnCoord S b
  have hrho : S.rho b.val = Point3.mk 0 r 0 := by
    apply Point3.ext
    · exact complementFaceReturn₁ S b.property.1 b.property.2.1
    · rfl
    · exact complementFaceReturn₃ S b.property.1 b.property.2.2.2
  have hr : r < pure2Intercept S := by
    apply (pure2_axis_mem_iff S r).mp
    rw [← hrho]
    exact S.rho_mem _
  have hresg : S.residue g = 0 := by
    rw [← S.residue_rho g, fullSupportBoundary_return_zero S hg hf]
    exact S.residue_zero
  have hsum : p+g = b.val+Point3.mk 0 g.y 0 := by
    ext <;> simp [p, Nat.sub_add_cancel ha, Nat.sub_add_cancel hb, b.property.2.2.1]
  have hres : S.residue p = S.residue (Point3.mk 0 (r+g.y) 0) := by
    calc
      S.residue p = S.residue (p+g) := by rw [S.residue_add,hresg]; simp
      _ = S.residue (b.val+Point3.mk 0 g.y 0) := by rw [hsum]
      _ = S.residue b.val+S.residue (Point3.mk 0 g.y 0) := S.residue_add _ _
      _ = S.residue (Point3.mk 0 r 0)+S.residue (Point3.mk 0 g.y 0) := by rw [← S.residue_rho b.val,hrho]
      _ = S.residue (Point3.mk 0 (r+g.y) 0) := by rw [← S.residue_add]; rfl
  have hout : Point3.mk 0 (r+g.y) 0 ∉ S.D := by
    intro hm
    have he := congrArg Point3.y (S.standard_eq_of_residue_eq hp hm hres)
    have := hf.2.1
    simp [p] at he
    omega
  have hl : pure2Intercept S ≤ r+g.y := by
    by_contra hn
    exact hout ((pure2_axis_mem_iff S _).mpr (by omega))
  exact ⟨by omega,hr⟩

/-- Two actual high corners cannot fit in the full-boundary rectangle. -/
theorem pair13_terminal_rectangle_separation (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (b c : Pair13Boundary S)
    (hba : g.x ≤ b.val.x) (hbb : g.z ≤ b.val.z)
    (hca : g.x ≤ c.val.x) (hcb : g.z ≤ c.val.z)
    (horder : b.val.x < c.val.x) :
    g.x < c.val.x-b.val.x ∨ g.z < b.val.z-c.val.z := by
  by_contra hn
  push Not at hn
  have hother := pair13_z_lt_of_x_lt S.down_closed
    (mem_pair13Boundaries.mpr b.property) (mem_pair13Boundaries.mpr c.property) horder
  let d := c.val.x-b.val.x
  let e := b.val.z-c.val.z
  let rb := pair13ReturnCoord S b
  let rc := pair13ReturnCoord S c
  have hb := pair13_high_return_bounds S hg hf b hba hbb
  have hc := pair13_high_return_bounds S hg hf c hca hcb
  have hbres : S.residue b.val = (rb : ZMod S.m)*S.p2 := by
    rw [← S.residue_rho b.val]
    simp [CyclicStaircase.residue,residueOf,complementFaceReturn₁ S b.property.1 b.property.2.1,
      complementFaceReturn₃ S b.property.1 b.property.2.2.2,rb,pair13ReturnCoord]
  have hcres : S.residue c.val = (rc : ZMod S.m)*S.p2 := by
    rw [← S.residue_rho c.val]
    simp [CyclicStaircase.residue,residueOf,complementFaceReturn₁ S c.property.1 c.property.2.1,
      complementFaceReturn₃ S c.property.1 c.property.2.2.2,rc,pair13ReturnCoord]
  have hda : (d : ZMod S.m)+b.val.x=c.val.x := by
    rw [← Nat.cast_add,show d+b.val.x=c.val.x by dsimp [d]; omega]
  have heb : (e : ZMod S.m)+c.val.z=b.val.z := by
    rw [← Nat.cast_add,show e+c.val.z=b.val.z by dsimp [e]; omega]
  simp only [CyclicStaircase.residue,residueOf,b.property.2.2.1,c.property.2.2.1,
    Nat.cast_zero,zero_mul,add_zero,zero_add] at hbres hcres
  by_cases hrc : rb ≤ rc
  · have hz : rc-rb < g.y := by dsimp [rb,rc] at *; omega
    have hr : ((rc-rb : ℕ) : ZMod S.m)+rb=rc := by rw [← Nat.cast_add,Nat.sub_add_cancel hrc]
    have hm1 : Point3.mk d 0 0 ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨by dsimp [d]; omega,Nat.zero_le _,Nat.zero_le _⟩,
        by intro he; have := congrArg Point3.z he; have := hf.2.2; simp_all⟩)
    have hm2 : Point3.mk 0 (rc-rb) e ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨Nat.zero_le _,Nat.le_of_lt hz,hn.2⟩,
        by intro he; have := congrArg Point3.x he; have := hf.1; simp_all⟩)
    have hres : S.residue (Point3.mk d 0 0) = S.residue (Point3.mk 0 (rc-rb) e) := by
      simp only [CyclicStaircase.residue,residueOf,Nat.cast_zero,zero_mul,add_zero,zero_add]
      linear_combination hcres-hbres+hda*S.p1-heb*S.p3-hr*S.p2
    have he := congrArg Point3.x (S.standard_eq_of_residue_eq hm1 hm2 hres)
    simp only at he
    dsimp [d] at he
    omega
  · have hz : rb-rc < g.y := by dsimp [rb,rc] at *; omega
    have hr : ((rb-rc : ℕ) : ZMod S.m)+rc=rb := by rw [← Nat.cast_add,Nat.sub_add_cancel (by omega : rc ≤ rb)]
    have hm1 : Point3.mk d (rb-rc) 0 ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨hn.1,Nat.le_of_lt hz,Nat.zero_le _⟩,
        by intro he; have := congrArg Point3.z he; have := hf.2.2; simp_all⟩)
    have hm2 : Point3.mk 0 0 e ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨Nat.zero_le _,Nat.zero_le _,hn.2⟩,
        by intro he; have := congrArg Point3.x he; have := hf.1; simp_all⟩)
    have hres : S.residue (Point3.mk d (rb-rc) 0) = S.residue (Point3.mk 0 0 e) := by
      simp only [CyclicStaircase.residue,residueOf,Nat.cast_zero,zero_mul,add_zero,zero_add]
      linear_combination hcres-hbres+hda*S.p1-heb*S.p3+hr*S.p2
    have he := congrArg Point3.x (S.standard_eq_of_residue_eq hm1 hm2 hres)
    simp only at he
    dsimp [d] at he
    omega

/-- Actual terminal return interval, without unit-weight assumptions. -/
theorem pair23_high_return_bounds (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (b : Pair23Boundary S) (ha : g.y ≤ b.val.y) (hb : g.z ≤ b.val.z) :
    pure1Intercept S-g.x ≤ pair23ReturnCoord S b ∧
    pair23ReturnCoord S b < pure1Intercept S := by
  let p := Point3.mk 0 (b.val.y-g.y) (b.val.z-g.z)
  have hp : p ∈ S.D := by
    apply S.down_closed (b := b.val.pred2) ?_ (b.property.1.pred2_mem b.property.2.2.1)
    exact ⟨by simp [p, Point3.pred2, b.property.2.1],by simp [p, Point3.pred2]; have := hf.2.1; omega,by simp [p, Point3.pred2]⟩
  let r := pair23ReturnCoord S b
  have hrho : S.rho b.val = Point3.mk r 0 0 := by
    apply Point3.ext
    · rfl
    · exact complementFaceReturn₂ S b.property.1 b.property.2.2.1
    · exact complementFaceReturn₃ S b.property.1 b.property.2.2.2
  have hr : r < pure1Intercept S := by
    apply (pure1_axis_mem_iff S r).mp
    rw [← hrho]
    exact S.rho_mem _
  have hresg : S.residue g = 0 := by
    rw [← S.residue_rho g, fullSupportBoundary_return_zero S hg hf]
    exact S.residue_zero
  have hsum : p+g = b.val+Point3.mk g.x 0 0 := by
    ext <;> simp [p, Nat.sub_add_cancel ha, Nat.sub_add_cancel hb, b.property.2.1]
  have hres : S.residue p = S.residue (Point3.mk (r+g.x) 0 0) := by
    calc
      S.residue p = S.residue (p+g) := by rw [S.residue_add,hresg]; simp
      _ = S.residue (b.val+Point3.mk g.x 0 0) := by rw [hsum]
      _ = S.residue b.val+S.residue (Point3.mk g.x 0 0) := S.residue_add _ _
      _ = S.residue (Point3.mk r 0 0)+S.residue (Point3.mk g.x 0 0) := by rw [← S.residue_rho b.val,hrho]
      _ = S.residue (Point3.mk (r+g.x) 0 0) := by rw [← S.residue_add]; rfl
  have hout : Point3.mk (r+g.x) 0 0 ∉ S.D := by
    intro hm
    have he := congrArg Point3.x (S.standard_eq_of_residue_eq hp hm hres)
    have := hf.1
    simp [p] at he
    omega
  have hl : pure1Intercept S ≤ r+g.x := by
    by_contra hn
    exact hout ((pure1_axis_mem_iff S _).mpr (by omega))
  exact ⟨by omega,hr⟩

/-- Two actual high corners cannot fit in the full-boundary rectangle. -/
theorem pair23_terminal_rectangle_separation (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hf : FullSupport g)
    (b c : Pair23Boundary S)
    (hba : g.y ≤ b.val.y) (hbb : g.z ≤ b.val.z)
    (hca : g.y ≤ c.val.y) (hcb : g.z ≤ c.val.z)
    (horder : b.val.y < c.val.y) :
    g.y < c.val.y-b.val.y ∨ g.z < b.val.z-c.val.z := by
  by_contra hn
  push Not at hn
  have hother := pair23_z_lt_of_y_lt S.down_closed
    (mem_pair23Boundaries.mpr b.property) (mem_pair23Boundaries.mpr c.property) horder
  let d := c.val.y-b.val.y
  let e := b.val.z-c.val.z
  let rb := pair23ReturnCoord S b
  let rc := pair23ReturnCoord S c
  have hb := pair23_high_return_bounds S hg hf b hba hbb
  have hc := pair23_high_return_bounds S hg hf c hca hcb
  have hbres : S.residue b.val = (rb : ZMod S.m)*S.p1 := by
    rw [← S.residue_rho b.val]
    simp [CyclicStaircase.residue,residueOf,complementFaceReturn₂ S b.property.1 b.property.2.2.1,
      complementFaceReturn₃ S b.property.1 b.property.2.2.2,rb,pair23ReturnCoord]
  have hcres : S.residue c.val = (rc : ZMod S.m)*S.p1 := by
    rw [← S.residue_rho c.val]
    simp [CyclicStaircase.residue,residueOf,complementFaceReturn₂ S c.property.1 c.property.2.2.1,
      complementFaceReturn₃ S c.property.1 c.property.2.2.2,rc,pair23ReturnCoord]
  have hda : (d : ZMod S.m)+b.val.y=c.val.y := by
    rw [← Nat.cast_add,show d+b.val.y=c.val.y by dsimp [d]; omega]
  have heb : (e : ZMod S.m)+c.val.z=b.val.z := by
    rw [← Nat.cast_add,show e+c.val.z=b.val.z by dsimp [e]; omega]
  simp only [CyclicStaircase.residue,residueOf,b.property.2.1,c.property.2.1,
    Nat.cast_zero,zero_mul,add_zero,zero_add] at hbres hcres
  by_cases hrc : rb ≤ rc
  · have hz : rc-rb < g.x := by dsimp [rb,rc] at *; omega
    have hr : ((rc-rb : ℕ) : ZMod S.m)+rb=rc := by rw [← Nat.cast_add,Nat.sub_add_cancel hrc]
    have hm1 : Point3.mk 0 d 0 ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨Nat.zero_le _,by dsimp [d]; omega,Nat.zero_le _⟩,
        by intro he; have := congrArg Point3.z he; have := hf.2.2; simp_all⟩)
    have hm2 : Point3.mk (rc-rb) 0 e ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨Nat.le_of_lt hz,Nat.zero_le _,hn.2⟩,
        by intro he; have := congrArg Point3.y he; have := hf.2.1; simp_all⟩)
    have hres : S.residue (Point3.mk 0 d 0) = S.residue (Point3.mk (rc-rb) 0 e) := by
      simp only [CyclicStaircase.residue,residueOf,Nat.cast_zero,zero_mul,add_zero,zero_add]
      linear_combination hcres-hbres+hda*S.p2-heb*S.p3-hr*S.p1
    have he := congrArg Point3.y (S.standard_eq_of_residue_eq hm1 hm2 hres)
    simp only at he
    dsimp [d] at he
    omega
  · have hz : rb-rc < g.x := by dsimp [rb,rc] at *; omega
    have hr : ((rb-rc : ℕ) : ZMod S.m)+rc=rb := by rw [← Nat.cast_add,Nat.sub_add_cancel (by omega : rc ≤ rb)]
    have hm1 : Point3.mk (rb-rc) d 0 ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨Nat.le_of_lt hz,hn.1,Nat.zero_le _⟩,
        by intro he; have := congrArg Point3.z he; have := hf.2.2; simp_all⟩)
    have hm2 : Point3.mk 0 0 e ∈ S.D := lowerBoxFinset_subset_D hg
      ((mem_lowerBoxFinset _ _).mpr ⟨⟨Nat.zero_le _,Nat.zero_le _,hn.2⟩,
        by intro he; have := congrArg Point3.y he; have := hf.2.1; simp_all⟩)
    have hres : S.residue (Point3.mk (rb-rc) d 0) = S.residue (Point3.mk 0 0 e) := by
      simp only [CyclicStaircase.residue,residueOf,Nat.cast_zero,zero_mul,add_zero,zero_add]
      linear_combination hcres-hbres+hda*S.p2-heb*S.p3+hr*S.p1
    have he := congrArg Point3.y (S.standard_eq_of_residue_eq hm1 hm2 hres)
    simp only at he
    dsimp [d] at he
    omega

end NSP3
