import NSP3.FiniteResidueCover
import NSP3.FastMandatorySeed

namespace NSP3

/-- A rejection certificate proposition with finite decidable branches. A split
must cover every compatible witness in U; it cannot silently omit a child. -/
def coverReject {m : ℕ} [NeZero m] : ℕ → FullResidualTuple → Point3 →
    ResidueWeights m → Finset Point3 → Finset Point3 → Prop
  | 0, q, g, _, _, A => A.card = m ∧ ¬ terminalMatches q m g A
  | fuel+1, q, g, w, U, A =>
      (A.card = m ∧ ¬ terminalMatches q m g A) ∨
      ∃ r ∈ (Finset.univ : Finset (ZMod m)),
        r ∉ A.image (residueWithWeights w) ∧
        ∀ p ∈ U,
          residueWithWeights w p = r →
          residueInjectiveOn (A ∪ fastSeedLowerBox p) w →
          ¬ g ≤ p →
          coverReject fuel q g w U (A ∪ fastSeedLowerBox p)

instance {m : ℕ} [NeZero m] (fuel : ℕ) (q : FullResidualTuple)
    (g : Point3) (w : ResidueWeights m) (U A : Finset Point3) :
    Decidable (coverReject fuel q g w U A) := by
  induction fuel generalizing A with
  | zero => unfold coverReject; infer_instance
  | succ fuel ih => unfold coverReject; infer_instance

/-- Soundness quantifies every bounded injective downset extension, not merely
the paths a generator decided to write. Candidate-universe coverage is explicit. -/
theorem coverReject_sound {m : ℕ} [NeZero m] (fuel : ℕ)
    (q : FullResidualTuple) (g : Point3) (w : ResidueWeights m)
    (U A D : Finset Point3) (hv : coverReject fuel q g w U A)
    (hd : IsDownset D) (hs : A ⊆ D) (hu : D ⊆ U)
    (hi : residueInjectiveOn D w) (hc : D.card = m) (hg : g ∉ D) :
    ¬ terminalMatches q m g D := by
  induction fuel generalizing A with
  | zero =>
      obtain ⟨ha,hn⟩ := hv
      have he : A = D := Finset.eq_of_subset_of_card_le hs (by omega)
      simpa [he] using hn
  | succ fuel ih =>
      rcases hv with ⟨ha,hn⟩ | ⟨r,_,hr,hbranches⟩
      · have he : A = D := Finset.eq_of_subset_of_card_le hs (by omega)
        simpa [he] using hn
      · have hrD : r ∈ D.image (residueWithWeights w) := by
          rw [residue_image_eq_univ w D hi hc]
          exact Finset.mem_univ r
        obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hrD
        have hsub : A ∪ fastSeedLowerBox p ⊆ D := by
          intro a ha
          rcases Finset.mem_union.mp ha with ha | ha
          · exact hs ha
          · rw [fastSeedLowerBox_eq,mem_seedLowerBox] at ha
            exact hd.mem_of_le ha hp
        have hij := residueInjectiveOn_mono w hsub hi
        have hng : ¬ g ≤ p := fun h => hg (hd.mem_of_le h hp)
        exact ih _ (hbranches p (hu hp) he hij hng) hsub

/-- Explicit machine-checkable Boolean interface. `of_decide_eq_true` is kernel
reflection, with the same completeness obligation on U as the soundness theorem. -/
def verifyCoverReject {m : ℕ} [NeZero m] (fuel : ℕ) (q : FullResidualTuple)
    (g : Point3) (w : ResidueWeights m) (U A : Finset Point3) : Bool :=
  decide (coverReject fuel q g w U A)

theorem verifyCoverReject_sound {m : ℕ} [NeZero m] (fuel : ℕ)
    (q : FullResidualTuple) (g : Point3) (w : ResidueWeights m)
    (U A D : Finset Point3) (hv : verifyCoverReject fuel q g w U A = true)
    (hd : IsDownset D) (hs : A ⊆ D) (hu : D ⊆ U)
    (hi : residueInjectiveOn D w) (hc : D.card = m) (hg : g ∉ D) :
    ¬ terminalMatches q m g D := by
  exact coverReject_sound fuel q g w U A D (of_decide_eq_true hv)
    hd hs hu hi hc hg

private theorem injective_insert_candidate {m bound : ℕ} (w : ResidueWeights m)
    (A : Finset Point3) (hi : residueInjectiveOn A w) (p : Point3)
    (hp : p ∈ extensionCandidates bound w A) : residueInjectiveOn (insert p A) w := by
  rw [residueInjectiveOn,Finset.card_image_iff] at hi ⊢
  have hf := (mem_extensionCandidates bound w A p).mp hp |>.2.2.2
  intro a ha b hb he
  rcases Finset.mem_insert.mp ha with ha | ha
  · subst a
    rcases Finset.mem_insert.mp hb with hb | hb
    · exact hb.symm
    · exact False.elim (hf (Finset.mem_image.mpr ⟨b,hb,he.symm⟩))
  · rcases Finset.mem_insert.mp hb with hb | hb
    · subst b
      exact False.elim (hf (Finset.mem_image.mpr ⟨a,ha,he⟩))
    · exact hi ha hb he

/-- Every member of the accepted recursion preserves all the invariants needed
by the cover verifier, including members never selected by an external search. -/
theorem completion_cover_invariants {m : ℕ} (fuel bound : ℕ)
    (w : ResidueWeights m) (U A D : Finset Point3) (ha : IsDownset A)
    (hi : residueInjectiveOn A w) (hau : A ⊆ U) (hbu : pointBox bound ⊆ U)
    (hD : D ∈ downsetCompletions fuel bound w A) :
    A ⊆ D ∧ IsDownset D ∧ residueInjectiveOn D w ∧ D ⊆ U := by
  induction fuel generalizing A with
  | zero =>
      have he : D = A := Finset.mem_singleton.mp hD
      subst D
      exact ⟨Finset.Subset.refl _,ha,hi,hau⟩
  | succ fuel ih =>
      obtain ⟨p,hp,hr⟩ := Finset.mem_biUnion.mp hD
      have hpu : p ∈ U := hbu ((mem_extensionCandidates bound w A p).mp hp).1
      have hsub : insert p A ⊆ U := Finset.insert_subset hpu hau
      obtain ⟨hAD,hd,hinj,hDU⟩ := ih (insert p A)
        (insert_isDownset_of_mem_extensionCandidates ha hp)
        (injective_insert_candidate w A hi p hp) hsub hr
      exact ⟨fun a h => hAD (Finset.mem_insert_of_mem h),hd,hinj,hDU⟩

theorem coverReject_excludes_completions {m : ℕ} [NeZero m] (fuel : ℕ)
    (q : FullResidualTuple) (g : Point3) (w : ResidueWeights m)
    (U A D : Finset Point3) (hv : coverReject fuel q g w U A)
    (ha : IsDownset A) (hi : residueInjectiveOn A w) (hau : A ⊆ U)
    (hbu : pointBox m ⊆ U) (hD : D ∈ downsetCompletions fuel m w A) :
    ¬ terminalMatches q m g D := by
  intro ht
  obtain ⟨hs,hd,hinj,hu⟩ := completion_cover_invariants fuel m w U A D ha hi hau hbu hD
  exact coverReject_sound fuel q g w U A D hv hd hs hu hinj ht.1 ht.2.1.not_mem ht

/-- Explicit remaining finite certificate obligation. This proposition is NOT
proved here, and is not replaced with the external 74/160-row count. -/
def GlobalCoverCertificates : Prop :=
  ∀ (q : FullResidualTuple) (m : ℕ) [NeZero m] (g : Point3) (w : ResidueWeights m),
    ReducedCheckerState q m g w →
    coverReject (m - (fastMandatorySeed q g).card) q g w
      (pointBox m ∪ fastMandatorySeed q g) (fastMandatorySeed q g)

theorem reducedNoTarget_of_globalCoverCertificates (h : GlobalCoverCertificates) :
    ReducedNoTarget := by
  intro q m hm g w hr D hD
  have hv := h q m g w hr
  rw [fastMandatorySeed_eq] at hv
  exact coverReject_excludes_completions (m - (mandatorySeed q g).card)
    q g w (pointBox m ∪ mandatorySeed q g) (mandatorySeed q g) D hv
    (mandatorySeed_isDownset q g) hr.1.2.2.2
    Finset.subset_union_right Finset.subset_union_left hD

end NSP3
