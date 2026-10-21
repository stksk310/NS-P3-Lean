import NSP3.FiniteCoordinateBounds

namespace NSP3

private def pointBoxEmbedding : (ℕ × (ℕ × ℕ)) ↪ Point3 where
  toFun a := Point3.mk a.1 a.2.1 a.2.2
  inj' := by
    intro a b h
    rcases a with ⟨ax, ⟨ay, az⟩⟩
    rcases b with ⟨bx, ⟨byc, bz⟩⟩
    simp only [Prod.mk.injEq]
    exact ⟨congrArg Point3.x h,
      ⟨congrArg Point3.y h, congrArg Point3.z h⟩⟩

/-- The transparent cubic point box with all coordinates strictly below `n`. -/
def pointBox (n : ℕ) : Finset Point3 :=
  ((Finset.range n).product ((Finset.range n).product (Finset.range n))).map
    pointBoxEmbedding

@[simp] theorem mem_pointBox (n : ℕ) (p : Point3) :
    p ∈ pointBox n ↔ p.x < n ∧ p.y < n ∧ p.z < n := by
  constructor
  · intro hp
    rcases Finset.mem_map.mp hp with ⟨a, ha, heq⟩
    rcases Finset.mem_product.mp ha with ⟨hx, hyz⟩
    rcases Finset.mem_product.mp hyz with ⟨hy, hz⟩
    simp only [Finset.mem_range] at hx hy hz
    subst p
    exact ⟨hx, hy, hz⟩
  · rintro ⟨hx, hy, hz⟩
    apply Finset.mem_map.mpr
    refine ⟨(p.x, (p.y, p.z)), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hx,
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr hy, Finset.mem_range.mpr hz⟩⟩
    · ext <;> rfl

/-- Every standard point lies in the parameter-sized box. -/
theorem standardSet_subset_pointBox_m (S : CyclicStaircase) :
    S.D ⊆ pointBox S.m := by
  intro q hq
  rw [mem_pointBox]
  exact ⟨standardPoint_x_lt_m S hq, standardPoint_y_lt_m S hq,
    standardPoint_z_lt_m S hq⟩

/-- A full-support minimal complement lies in the successor parameter box. -/
theorem fullSupport_minimalComplement_mem_pointBox_succ_m
    (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    g ∈ pointBox (S.m + 1) := by
  rw [mem_pointBox]
  exact ⟨Nat.lt_succ_of_le (fullSupport_minimalComplement_x_le_m S hg hfull),
    Nat.lt_succ_of_le (fullSupport_minimalComplement_y_le_m S hg hfull),
    Nat.lt_succ_of_le (fullSupport_minimalComplement_z_le_m S hg hfull)⟩

/-- Canonical finite specification of minimal complements inside a proved point box.
It is intentionally noncomputable because `MinimalComplement` is proposition-valued. -/
noncomputable def boundedMinimalComplements (n : ℕ) (D : Finset Point3) : Finset Point3 := by
  classical
  exact (pointBox n).filter (MinimalComplement D)

@[simp] theorem mem_boundedMinimalComplements (n : ℕ) (D : Finset Point3) (p : Point3) :
    p ∈ boundedMinimalComplements n D ↔
      p.x < n ∧ p.y < n ∧ p.z < n ∧ MinimalComplement D p := by
  simp [boundedMinimalComplements, and_assoc]

/-- Under strict failure, every standard point lies in the globally justified `307³` box. -/
theorem strictFailure_D_subset_pointBox307 (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hstrict : S.m < fullTarget S) :
    S.D ⊆ pointBox 307 := by
  intro q hq
  rw [mem_pointBox]
  have hm := fullSupport_strictFailure_m_le_306 S hg hfull hord hstrict
  exact ⟨by have := standardPoint_x_lt_m S hq; omega,
    by have := standardPoint_y_lt_m S hq; omega,
    by have := standardPoint_z_lt_m S hq; omega⟩

/-- The distinguished full boundary itself is also inside the justified box. -/
theorem strictFailure_fullBoundary_mem_pointBox307 (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hstrict : S.m < fullTarget S) :
    g ∈ pointBox 307 := by
  rw [mem_pointBox]
  have hm := fullSupport_strictFailure_m_le_306 S hg hfull hord hstrict
  exact ⟨by have := fullSupport_minimalComplement_x_le_m S hg hfull; omega,
    by have := fullSupport_minimalComplement_y_le_m S hg hfull; omega,
    by have := fullSupport_minimalComplement_z_le_m S hg hfull; omega⟩

/-- Hence the canonical bounded boundary specification contains the actual full boundary. -/
theorem strictFailure_fullBoundary_mem_boundedMinimalComplements307
    (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (hstrict : S.m < fullTarget S) :
    g ∈ boundedMinimalComplements 307 S.D := by
  rw [mem_boundedMinimalComplements]
  have hm := fullSupport_strictFailure_m_le_306 S hg hfull hord hstrict
  exact ⟨by have := fullSupport_minimalComplement_x_le_m S hg hfull; omega,
    by have := fullSupport_minimalComplement_y_le_m S hg hfull; omega,
    by have := fullSupport_minimalComplement_z_le_m S hg hfull; omega, hg⟩

end NSP3
