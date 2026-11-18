import NSP3.V03.CornerBound
import NSP3.V03.Main
import NSP3.V03.BettiWindows

namespace NSP3.V03

theorem cyclic_full_corners_card_le_one (S : CyclicStaircase) :
    (fullSupportCorners S.D).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  obtain ⟨hp,hpf⟩ := (mem_fullSupportCorners _ _).mp hp
  obtain ⟨hq,hqf⟩ := (mem_fullSupportCorners _ _).mp hq
  exact fullSupportBoundary_unique S hp hpf hq hqf

theorem cyclic_maximalPoints_bound (S : CyclicStaircase) :
    (maximalPoints S.D).card ≤ T S.m-1 := by
  classical
  have hcorn := maximalPoints_card_add_two_le_boundary S.down_closed ⟨_,S.zero_mem⟩
  have hfull := cyclic_full_corners_card_le_one S
  have he : Nat.card {p : Point3 // MinimalComplement S.D p}=(cornerBoundary S.D).card :=
    Nat.subtype_card _ (mem_cornerBoundary S.D)
  have hcap := cyclicStaircase_boundary_card_sharp S
  rw [he] at hcap
  change (cornerBoundary S.D).card ≤ T S.m at hcap
  omega

theorem cyclic_maximalPoints_noFull_bound (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) : (maximalPoints S.D).card ≤ T S.m-2 := by
  classical
  have hcorn := maximalPoints_card_add_two_le_boundary S.down_closed ⟨_,S.zero_mem⟩
  have hempty : fullSupportCorners S.D=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp,hpf⟩ := (mem_fullSupportCorners _ _).mp hp
    exact hnf ⟨p,hp,hpf⟩
  rw [hempty,Finset.card_empty,Nat.add_zero] at hcorn
  have he : Nat.card {p : Point3 // MinimalComplement S.D p}=(cornerBoundary S.D).card :=
    Nat.subtype_card _ (mem_cornerBoundary S.D)
  have hcap := cyclicStaircase_boundary_card_sharp S
  rw [he] at hcap
  change (cornerBoundary S.D).card ≤ T S.m at hcap
  omega

/-- A bound on the actual PF-set cardinality, independent of a Tor identification. -/
theorem pseudoFrobeniusType_upper (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    pseudoFrobeniusType m a b c ≤ T m-1 := by
  have htype := pseudoFrobeniusType_le_maximalPoints m a b c h.positive
    (by have := h.least_a; have := h.positive; omega)
    (by have := h.least_b; have := h.positive; omega)
    (by have := h.least_c; have := h.positive; omega) h.coprime
  exact htype.trans (cyclic_maximalPoints_bound (aperyCyclicStaircase m a b c h.positive h.coprime))

theorem pseudoFrobeniusType_noFull_upper (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c)
    (hnf : NoFullSupportBoundary (aperyCyclicStaircase m a b c h.positive h.coprime)) :
    pseudoFrobeniusType m a b c ≤ T m-2 := by
  have htype := pseudoFrobeniusType_le_maximalPoints m a b c h.positive
    (by have := h.least_a; have := h.positive; omega)
    (by have := h.least_b; have := h.positive; omega)
    (by have := h.least_c; have := h.positive; omega) h.coprime
  exact htype.trans (cyclic_maximalPoints_noFull_bound
    (aperyCyclicStaircase m a b c h.positive h.coprime) hnf)

/-- The same PF invariant on arbitrary semigroup sets. -/
noncomputable def semigroupType (S : Set ℕ) : ℕ :=
  ({f : ℕ | f∉S ∧ ∀ s∈S, 0 < s → f+s∈S} : Set ℕ).ncard

theorem semigroupType_generated (m a b c : ℕ) :
    semigroupType (generatedSemigroup m a b c)=pseudoFrobeniusType m a b c := rfl

theorem numerical_semigroup_type_upper (S : AddSubmonoid ℕ) (m : ℕ)
    (hcof : ((S : Set ℕ)ᶜ).Finite)
    (hedim : semigroupEmbeddingDimension (S : Set ℕ)=4)
    (hm : IsSemigroupMultiplicity (S : Set ℕ) m) :
    semigroupType (S : Set ℕ) ≤ T m-1 := by
  obtain ⟨a,b,c,h,heq⟩ := numerical_semigroup_class_coverage S m hcof hedim hm
  have hset : generatedSemigroup m a b c=(S : Set ℕ) :=
    congrArg (fun U : AddSubmonoid ℕ => (U : Set ℕ)) heq
  rw [← hset,semigroupType_generated]
  exact pseudoFrobeniusType_upper m a b c h

theorem T_ge_six (m : ℕ) (hm : 4 ≤ m) : 6 ≤ T m := by
  have hs : 4 ≤ Nat.sqrt (4*m) := Nat.le_sqrt.mpr (by nlinarith)
  unfold T
  omega

theorem T_square_bound (m : ℕ) : (T m-2)^2 ≤ 4*m := by
  have hs := Nat.le_sqrt.mp (le_refl (Nat.sqrt (4*m)))
  have he : T m-2=Nat.sqrt (4*m) := by unfold T; omega
  simpa only [he,pow_two] using hs

/-- An actual extremal-presentation family supplies the lower type window. -/
theorem extremal_presentation_type_realized (m : ℕ) (hm : 4 ≤ m) :
    ∃ a b c, ∃ h : MinimalFourGeneratorClass m a b c,
      intrinsicRho (generatedSemigroup m a b c)=T m ∧
      pseudoFrobeniusType m a b c=T m-3 :=
  presentation_type_window m (T m) (T_ge_six m hm) (T_square_bound m)

end NSP3.V03
