import NSP3.FiniteReducedComposition

namespace NSP3

/-- Candidate points whose entire inclusive lower box can coexist injectively
with the seed. This definition is a coverage specification, not a claim that
materializing the whole ambient cube is a fast final enumerator. -/
def admissibleCoverPoints {m : ℕ} (bound : ℕ) (w : ResidueWeights m)
    (A : Finset Point3) (g : Point3) : Finset Point3 :=
  (pointBox bound).filter fun p =>
    ¬ g ≤ p ∧ residueInjectiveOn (A ∪ seedLowerBox p) w

theorem residueInjectiveOn_mono {m : ℕ} (w : ResidueWeights m)
    {A D : Finset Point3} (hs : A ⊆ D) (hi : residueInjectiveOn D w) :
    residueInjectiveOn A w := by
  rw [residueInjectiveOn,Finset.card_image_iff] at hi ⊢
  exact fun a ha b hb heq => hi (hs ha) (hs hb) heq

theorem downset_subset_admissibleCoverPoints {m : ℕ} (w : ResidueWeights m)
    {A D : Finset Point3} {g : Point3} (hd : IsDownset D) (hs : A ⊆ D)
    (hb : D ⊆ pointBox m) (hi : residueInjectiveOn D w) (hg : g ∉ D) :
    D ⊆ admissibleCoverPoints m w A g := by
  intro p hp
  apply Finset.mem_filter.mpr
  refine ⟨hb hp,?_,?_⟩
  · exact fun hgp => hg (hd.mem_of_le hgp hp)
  · apply residueInjectiveOn_mono w (D := D) _ hi
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact hs ha
    · exact hd.mem_of_le ((mem_seedLowerBox p a).mp ha) hp

/-- Injectivity on exactly m points forces coverage of every cyclic residue. -/
theorem residue_image_eq_univ {m : ℕ} [NeZero m] (w : ResidueWeights m)
    (D : Finset Point3) (hi : residueInjectiveOn D w) (hc : D.card = m) :
    D.image (residueWithWeights w) = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ,ZMod.card,hi,hc]

theorem admissibleCoverPoints_hit_every_residue {m : ℕ} [NeZero m]
    (w : ResidueWeights m) {A D : Finset Point3} {g : Point3}
    (hd : IsDownset D) (hs : A ⊆ D) (hb : D ⊆ pointBox m)
    (hi : residueInjectiveOn D w) (hg : g ∉ D) (hc : D.card = m) (r : ZMod m) :
    ∃ p ∈ admissibleCoverPoints m w A g, residueWithWeights w p = r := by
  have hr : r ∈ D.image (residueWithWeights w) := by
    rw [residue_image_eq_univ w D hi hc]
    exact Finset.mem_univ r
  obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp hr
  exact ⟨p,downset_subset_admissibleCoverPoints w hd hs hb hi hg hp,heq⟩

theorem no_completion_of_missing_admissible_residue {m : ℕ} [NeZero m]
    (w : ResidueWeights m) {A D : Finset Point3} {g : Point3}
    (hd : IsDownset D) (hs : A ⊆ D) (hb : D ⊆ pointBox m)
    (hi : residueInjectiveOn D w) (hg : g ∉ D) (hc : D.card = m) (r : ZMod m)
    (hr : ∀ p ∈ admissibleCoverPoints m w A g, residueWithWeights w p ≠ r) : False := by
  obtain ⟨p,hp,heq⟩ := admissibleCoverPoints_hit_every_residue w hd hs hb hi hg hc r
  exact hr p hp heq

end NSP3
