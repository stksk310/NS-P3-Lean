import NSP3.RhoTransport

namespace NSP3

def IsAtomPresentation (S : Set ℕ) (R : Finset (AtomCoefficients S × AtomCoefficients S)) : Prop :=
  ∀ u v, GeneratedAddRel R u v ↔ atomWeight S u = atomWeight S v

/-- Minimum finite presentation cardinal for the numeric map on actual atom coefficients.
The empty existence-domain convention is not used in the bridge or bound. -/
noncomputable def intrinsicRho (S : Set ℕ) : ℕ :=
  sInf {n : ℕ | ∃ R : Finset (AtomCoefficients S × AtomCoefficients S),
    IsAtomPresentation S R ∧ R.card = n}

theorem factorPresentation_transport_iff (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (R : Finset (Fact4 × Fact4)) :
    IsAtomPresentation (generatedSemigroup m a b c) (mapRelations (atomFactorEquiv m a b c h) R) ↔
      IsFactorPresentation m a b c R := by
  let e := atomFactorEquiv m a b c h
  constructor
  · intro hp u v
    rw [← generatedAddRel_four_iff, ← generatedAddRel_map_iff e R u v]
    exact (hp (e u) (e v)).trans (by rw [atomFactorEquiv_weight, atomFactorEquiv_weight])
  · intro hp u v
    obtain ⟨u,rfl⟩ := e.surjective u
    obtain ⟨v,rfl⟩ := e.surjective v
    rw [generatedAddRel_map_iff, generatedAddRel_four_iff, hp]
    rw [atomFactorEquiv_weight, atomFactorEquiv_weight]

theorem atomPresentation_pullback_iff (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (R : Finset (AtomCoefficients (generatedSemigroup m a b c) ×
      AtomCoefficients (generatedSemigroup m a b c))) :
    IsFactorPresentation m a b c (mapRelations (atomFactorEquiv m a b c h).symm R) ↔
      IsAtomPresentation (generatedSemigroup m a b c) R := by
  rw [← factorPresentation_transport_iff m a b c h]
  have he : mapRelations (atomFactorEquiv m a b c h)
      (mapRelations (atomFactorEquiv m a b c h).symm R) = R :=
    mapRelations_symm (atomFactorEquiv m a b c h).symm R
  rw [he]

theorem atomPresentation_card_spectrum (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    {n : ℕ | ∃ R : Finset (AtomCoefficients (generatedSemigroup m a b c) ×
        AtomCoefficients (generatedSemigroup m a b c)),
      IsAtomPresentation (generatedSemigroup m a b c) R ∧ R.card = n} =
    {n : ℕ | ∃ R : Finset (Fact4 × Fact4), IsFactorPresentation m a b c R ∧ R.card = n} := by
  ext n
  constructor
  · rintro ⟨R,hR,hcard⟩
    exact ⟨mapRelations (atomFactorEquiv m a b c h).symm R,
      (atomPresentation_pullback_iff m a b c h R).mpr hR, (mapRelations_card _ _).trans hcard⟩
  · rintro ⟨R,hR,hcard⟩
    exact ⟨mapRelations (atomFactorEquiv m a b c h) R,
      (factorPresentation_transport_iff m a b c h R).mpr hR, (mapRelations_card _ _).trans hcard⟩

theorem literature_rho_identification (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    intrinsicRho (generatedSemigroup m a b c) = minimumFourInputRelations m a b c := by
  unfold intrinsicRho minimumFourInputRelations
  rw [atomPresentation_card_spectrum m a b c h]

theorem intrinsicRho_attained (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    ∃ R : Finset (AtomCoefficients (generatedSemigroup m a b c) ×
      AtomCoefficients (generatedSemigroup m a b c)),
      IsAtomPresentation (generatedSemigroup m a b c) R ∧
      R.card = intrinsicRho (generatedSemigroup m a b c) := by
  obtain ⟨R,hR,hcard⟩ := minimumFourInputRelations_attained m a b c h.positive h.coprime
  refine ⟨mapRelations (atomFactorEquiv m a b c h) R,
    (factorPresentation_transport_iff m a b c h R).mpr hR, ?_⟩
  rw [mapRelations_card, hcard, literature_rho_identification m a b c h]

theorem intrinsicRho_le (S : Set ℕ) (R : Finset (AtomCoefficients S × AtomCoefficients S))
    (hR : IsAtomPresentation S R) : intrinsicRho S ≤ R.card :=
  Nat.sInf_le ⟨R,hR,rfl⟩

/-- A cardinal-minimum presentation is also inclusion-minimal. This does not assert
that every inclusion-minimal presentation has the same cardinality. -/
theorem intrinsicRho_minimal_attained (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    ∃ R : Finset (AtomCoefficients (generatedSemigroup m a b c) ×
      AtomCoefficients (generatedSemigroup m a b c)),
      IsAtomPresentation (generatedSemigroup m a b c) R ∧
      R.card = intrinsicRho (generatedSemigroup m a b c) ∧
      ∀ T, T ⊂ R → ¬ IsAtomPresentation (generatedSemigroup m a b c) T := by
  obtain ⟨R,hR,hcard⟩ := intrinsicRho_attained m a b c h
  refine ⟨R,hR,hcard,?_⟩
  intro T hT hp
  have hlt := Finset.card_lt_card hT
  have hle := intrinsicRho_le _ T hp
  omega

theorem intrinsic_rho_sharp (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    intrinsicRho (generatedSemigroup m a b c) ≤ 2 + Nat.sqrt (4*m) := by
  rw [literature_rho_identification m a b c h]
  exact minimal_presentation_four_input_sharp m a b c h.positive h.coprime

theorem intrinsic_rho_real_sharp (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    intrinsicRho (generatedSemigroup m a b c) ≤ ⌊(2 : ℝ)+2*Real.sqrt (m : ℝ)⌋₊ := by
  rw [literature_rho_identification m a b c h]
  exact minimal_presentation_four_input_real_sharp m a b c h.positive h.coprime

end NSP3
