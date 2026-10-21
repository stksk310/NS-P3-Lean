import NSP3.ResidueCoverCertificate

namespace NSP3

theorem card_fastSeedLowerBox (p : Point3) :
    (fastSeedLowerBox p).card = (p.x+1)*(p.y+1)*(p.z+1) := by
  unfold fastSeedLowerBox seedRect
  have hinj : Function.Injective (fun a : ℕ × (ℕ × ℕ) =>
      Point3.mk a.1 a.2.1 a.2.2) := by
    intro a b h
    apply Prod.ext
    · exact congrArg Point3.x h
    · apply Prod.ext
      · exact congrArg Point3.y h
      · exact congrArg Point3.z h
  rw [Finset.card_image_of_injective _ hinj]
  simp only [Finset.product_eq_sprod,Finset.card_product,Finset.card_range,Nat.mul_assoc]

/-- Inclusive volume bound, including points on coordinate planes and axes. -/
def productVolumePoints (m : ℕ) : Finset Point3 :=
  ((Finset.range m).biUnion fun x =>
    (Finset.range (m/(x+1))).biUnion fun y =>
      (Finset.range (m/((x+1)*(y+1)))).image fun z =>
        (⟨x,y,z⟩ : Point3)).filter fun p => (p.x+1)*(p.y+1)*(p.z+1) ≤ m

theorem mem_productVolumePoints (m : ℕ) (p : Point3) :
    p ∈ productVolumePoints m ↔ (p.x+1)*(p.y+1)*(p.z+1) ≤ m := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro hp
    have hxy : (p.x+1)*(p.y+1) ≤ m := by
      nlinarith [Nat.zero_le ((p.x+1)*(p.y+1)*p.z)]
    have hx : p.x+1 ≤ m := by nlinarith [Nat.zero_le ((p.x+1)*p.y)]
    have hy : p.y+1 ≤ m/(p.x+1) := by
      apply (Nat.le_div_iff_mul_le (by omega)).mpr
      simpa only [Nat.mul_comm] using hxy
    have hz : p.z+1 ≤ m/((p.x+1)*(p.y+1)) := by
      apply (Nat.le_div_iff_mul_le (by positivity)).mpr
      simpa only [Nat.mul_comm] using hp
    refine Finset.mem_filter.mpr ⟨?_,hp⟩
    refine Finset.mem_biUnion.mpr ⟨p.x,Finset.mem_range.mpr (by omega),?_⟩
    refine Finset.mem_biUnion.mpr ⟨p.y,Finset.mem_range.mpr (by omega),?_⟩
    exact Finset.mem_image.mpr ⟨p.z,Finset.mem_range.mpr (by omega),by cases p; rfl⟩

def compactCoverPoints {m : ℕ} (w : ResidueWeights m)
    (A : Finset Point3) (g : Point3) : Finset Point3 :=
  let used := A.image (residueWithWeights w)
  (productVolumePoints m).filter fun p =>
    ¬ g ≤ p ∧ (p ∈ A ∨ (residueWithWeights w p ∉ used ∧
      residueInjectiveOn (A ∪ fastSeedLowerBox p) w))

/-- Every final downset of m points is covered. No externally selected universe
and no coordinate-unit hypothesis enters this bound. -/
theorem downset_subset_compactCoverPoints {m : ℕ} (w : ResidueWeights m)
    (A D : Finset Point3) (g : Point3) (hd : IsDownset D) (hs : A ⊆ D)
    (hi : residueInjectiveOn D w) (hc : D.card = m) (hg : g ∉ D) :
    D ⊆ compactCoverPoints w A g := by
  intro p hp
  have hb : fastSeedLowerBox p ⊆ D := by
    intro a ha
    rw [fastSeedLowerBox_eq,mem_seedLowerBox] at ha
    exact hd.mem_of_le ha hp
  have hsub : A ∪ fastSeedLowerBox p ⊆ D := Finset.union_subset hs hb
  refine Finset.mem_filter.mpr ⟨?_,fun h => hg (hd.mem_of_le h hp),?_⟩
  · rw [mem_productVolumePoints,← card_fastSeedLowerBox,← hc]
    exact Finset.card_le_card hb
  · by_cases hpA : p ∈ A
    · exact Or.inl hpA
    · refine Or.inr ⟨?_,residueInjectiveOn_mono w hsub hi⟩
      intro hr
      obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hr
      have heq : a = p := (Finset.card_image_iff.mp hi) (hs ha) hp he
      exact hpA (heq ▸ ha)

theorem compactCoverReject_excludes_completions {m : ℕ} [NeZero m]
    (fuel : ℕ) (q : FullResidualTuple) (g : Point3) (w : ResidueWeights m)
    (A D : Finset Point3) (ha : IsDownset A) (hi : residueInjectiveOn A w)
    (hv : coverReject fuel q g w (compactCoverPoints w A g) A)
    (hD : D ∈ downsetCompletions fuel m w A) : ¬ terminalMatches q m g D := by
  intro ht
  obtain ⟨hs,hd,hinj,_⟩ := completion_cover_invariants fuel m w
    (pointBox m ∪ A) A D ha hi Finset.subset_union_right Finset.subset_union_left hD
  have hu := downset_subset_compactCoverPoints w A D g hd hs hinj ht.1 ht.2.1.not_mem
  exact coverReject_sound fuel q g w _ A D hv hd hs hu hinj ht.1 ht.2.1.not_mem ht

end NSP3
