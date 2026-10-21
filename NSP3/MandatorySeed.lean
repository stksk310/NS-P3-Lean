import NSP3.FiniteCheckerState
import NSP3.CoreHole

namespace NSP3

/-- The points forced solely by a residual triple and the distinguished full
boundary.  The clauses are the punctured lower box, the three forced axis
segments, the three Ferrers triangles, and the punctured full core. -/
def MandatorySeedPred (q : FullResidualTuple) (g p : Point3) : Prop :=
  (p ≤ g ∧ p ≠ g) ∨
  (p.y = 0 ∧ p.z = 0 ∧ p.x ≤ q.r) ∨
  (p.x = 0 ∧ p.z = 0 ∧ p.y ≤ q.r) ∨
  (p.x = 0 ∧ p.y = 0 ∧ p.z ≤ q.s) ∨
  (0 < p.x ∧ 0 < p.y ∧ p.z = 0 ∧ p.x + p.y ≤ q.r) ∨
  (0 < p.x ∧ p.y = 0 ∧ 0 < p.z ∧ p.x + p.z ≤ q.s) ∨
  (p.x = 0 ∧ 0 < p.y ∧ 0 < p.z ∧ p.y + p.z ≤ q.t) ∨
  (0 < p.x ∧ 0 < p.y ∧ 0 < p.z ∧
    p.x + p.y ≤ q.r ∧ p.x + p.z ≤ q.s ∧ p.y + p.z ≤ q.t ∧
    ¬ g ≤ p)

private instance point3LEDecidable (a b : Point3) : Decidable (a ≤ b) := by
  change Decidable (a.x ≤ b.x ∧ a.y ≤ b.y ∧ a.z ≤ b.z)
  infer_instance

instance (q : FullResidualTuple) (g p : Point3) :
    Decidable (MandatorySeedPred q g p) := by
  unfold MandatorySeedPred
  infer_instance

private def mandatorySeedBound (q : FullResidualTuple) (g : Point3) : ℕ :=
  q.r + q.s + q.t + g.x + g.y + g.z + 2

/-- The finite collection of directly forced points before down-closure. -/
def rawMandatorySeed (q : FullResidualTuple) (g : Point3) : Finset Point3 :=
  (pointBox (mandatorySeedBound q g)).filter (MandatorySeedPred q g)

private theorem mandatorySeedPred_lt_bound {q : FullResidualTuple} {g p : Point3}
    (hp : MandatorySeedPred q g p) :
    p.x < mandatorySeedBound q g ∧ p.y < mandatorySeedBound q g ∧
      p.z < mandatorySeedBound q g := by
  unfold MandatorySeedPred at hp
  unfold mandatorySeedBound
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp
  · rcases hp with ⟨⟨hx, hy, hz⟩, -⟩
    exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega⟩
  · exact ⟨by omega, by omega, by omega⟩

@[simp] theorem mem_rawMandatorySeed (q : FullResidualTuple) (g p : Point3) :
    p ∈ rawMandatorySeed q g ↔ MandatorySeedPred q g p := by
  constructor
  · exact fun hp => (Finset.mem_filter.mp hp).2
  · intro hp
    exact Finset.mem_filter.mpr ⟨(mem_pointBox _ _).mpr
      (mandatorySeedPred_lt_bound hp), hp⟩

/-- Inclusive coordinatewise lower box, implemented without classical choice. -/
def seedLowerBox (p : Point3) : Finset Point3 :=
  (pointBox (p.x + p.y + p.z + 1)).filter fun a => a ≤ p

@[simp] theorem mem_seedLowerBox (p a : Point3) :
    a ∈ seedLowerBox p ↔ a ≤ p := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    rcases h with ⟨hx, hy, hz⟩
    exact Finset.mem_filter.mpr
      ⟨(mem_pointBox _ _).mpr ⟨by omega, by omega, by omega⟩,
        ⟨hx, hy, hz⟩⟩

/-- Computable downward closure of all universally forced seed points.  The
`biUnion` representation avoids scanning a large ambient cube for every seed
membership query. -/
def mandatorySeed (q : FullResidualTuple) (g : Point3) : Finset Point3 :=
  (rawMandatorySeed q g).biUnion seedLowerBox

@[simp] theorem mem_mandatorySeed (q : FullResidualTuple) (g p : Point3) :
    p ∈ mandatorySeed q g ↔
      ∃ b ∈ rawMandatorySeed q g, p ≤ b := by
  constructor
  · intro hp
    rcases Finset.mem_biUnion.mp hp with ⟨b, hb, hpb⟩
    exact ⟨b, hb, (mem_seedLowerBox b p).mp hpb⟩
  · rintro ⟨b, hb, hpb⟩
    exact Finset.mem_biUnion.mpr ⟨b, hb, (mem_seedLowerBox b p).mpr hpb⟩

theorem lowerBoxFinset_subset_mandatorySeed (q : FullResidualTuple) (g : Point3) :
    lowerBoxFinset g ⊆ mandatorySeed q g := by
  intro p hp
  rw [mem_mandatorySeed]
  refine ⟨p, ?_, le_rfl⟩
  rw [mem_rawMandatorySeed]
  exact Or.inl ((mem_lowerBoxFinset g p).mp hp)

theorem mandatorySeed_isDownset (q : FullResidualTuple) (g : Point3) :
    IsDownset (mandatorySeed q g) := by
  intro a b hab hb
  rw [mem_mandatorySeed] at hb ⊢
  rcases hb with ⟨c, hc, hbc⟩
  exact ⟨c, hc, le_trans hab hbc⟩

/-- The parametric mandatory seed of every actual full boundary is contained
in the staircase. -/
theorem mandatorySeed_subset_standardSet (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    mandatorySeed
      (FullResidualTuple.mk (pair12Count S.D) (pair13Count S.D)
        (pair23Count S.D)) g ⊆ S.D := by
  intro p hp
  rcases (mem_mandatorySeed _ _ _).mp hp with ⟨b, hb, hpb⟩
  apply S.down_closed.mem_of_le hpb
  rw [mem_rawMandatorySeed] at hb
  unfold MandatorySeedPred at hb
  rcases hb with hb | hb | hb | hb | hb | hb | hb | hb
  · exact lowerBoxFinset_subset_D hg ((mem_lowerBoxFinset g b).mpr hb)
  · have heq : Point3.mk b.x 0 0 = b := by
      ext <;> simp [hb.1, hb.2.1]
    rw [← heq]
    apply (pure1_axis_mem_iff S b.x).mpr
    have := pair12_intercept1_lower S
    have hbr : b.x ≤ pair12Count S.D := by simpa using hb.2.2
    omega
  · have heq : Point3.mk 0 b.y 0 = b := by
      ext <;> simp [hb.1, hb.2.1]
    rw [← heq]
    apply (pure2_axis_mem_iff S b.y).mpr
    have := pair12_intercept2_lower S
    have hbr : b.y ≤ pair12Count S.D := by simpa using hb.2.2
    omega
  · have heq : Point3.mk 0 0 b.z = b := by
      ext <;> simp [hb.1, hb.2.1]
    rw [← heq]
    apply (pure3_axis_mem_iff S b.z).mpr
    have := pair13_intercept3_lower S
    have hbs : b.z ≤ pair13Count S.D := by simpa using hb.2.2
    omega
  · have hsum : b.x + b.y ≤ pair12Count S.D := by simpa using hb.2.2.2
    have hmem := pair12Triangle_subset S.down_closed hb.1 hb.2.1 hsum
    have heq : Point3.mk b.x b.y 0 = b := by ext <;> simp [hb.2.2.1]
    exact heq ▸ hmem
  · have hsum : b.x + b.z ≤ pair13Count S.D := by simpa using hb.2.2.2
    have hmem := pair13Triangle_subset S.down_closed hb.1 hb.2.2.1 hsum
    have heq : Point3.mk b.x 0 b.z = b := by ext <;> simp [hb.2.1]
    exact heq ▸ hmem
  · have hsum : b.y + b.z ≤ pair23Count S.D := by simpa using hb.2.2.2
    have hmem := pair23Triangle_subset S.down_closed hb.2.1 hb.2.2.1 hsum
    have heq : Point3.mk 0 b.y b.z = b := by ext <;> simp [hb.1]
    exact heq ▸ hmem
  · apply fullSupport_puncturedCore_mem S hg hfull
    exact ⟨⟨hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1,
      hb.2.2.2.2.1, hb.2.2.2.2.2.1⟩, hb.2.2.2.2.2.2⟩

end NSP3
