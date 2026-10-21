import NSP3.CommonCardLayers

namespace NSP3.CommonCard

theorem numericPresentation_transport {A B : Type*} [Add A] [Add B]
    (e : A ≃+ B) (w : A → ℕ) (z : B → ℕ) (hw : ∀ u, z (e u) = w u)
    (R : Finset (A × A)) :
    NumericPresentation z (mapRelations e R) ↔ NumericPresentation w R := by
  constructor
  · intro hp u v
    calc
      GeneratedAddRel R u v ↔ GeneratedAddRel (mapRelations e R) (e u) (e v) :=
        (generatedAddRel_map_iff e R u v).symm
      _ ↔ z (e u) = z (e v) := hp _ _
      _ ↔ w u = w v := by rw [hw u,hw v]
  · intro hp u v
    obtain ⟨u,rfl⟩ := e.surjective u
    obtain ⟨v,rfl⟩ := e.surjective v
    rw [generatedAddRel_map_iff, hp, hw u, hw v]

theorem numeric_minimal_transport {A B : Type*} [Add A] [Add B]
    (e : A ≃+ B) (w : A → ℕ) (z : B → ℕ) (hw : ∀ u, z (e u) = w u)
    (R : Finset (A × A))
    (hmin : ∀ P, P ⊂ R → ¬ NumericPresentation w P) :
    ∀ P, P ⊂ mapRelations e R → ¬ NumericPresentation z P := by
  intro P hP hp
  have hs : mapRelations e.symm P ⊂ mapRelations e.symm (mapRelations e R) :=
    Finset.map_ssubset_map.mpr hP
  rw [mapRelations_symm] at hs
  apply hmin _ hs
  have ht := numericPresentation_transport e w z hw (mapRelations e.symm P)
  have hm : mapRelations e (mapRelations e.symm P) = P := mapRelations_symm e.symm P
  rw [hm] at ht
  exact ht.mp hp

noncomputable def atomToFour (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    AtomCoefficients (generatedSemigroup m a b c) ≃+ FourCoeff :=
  (atomFactorEquiv m a b c h).symm.trans fourCoordinates

theorem atomToFour_weight (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (u : AtomCoefficients (generatedSemigroup m a b c)) :
    degree ![m,a,b,c] (atomToFour m a b c h u) = atomWeight (generatedSemigroup m a b c) u := by
  change degree ![m,a,b,c] (fourCoordinates ((atomFactorEquiv m a b c h).symm u)) = _
  rw [degree_fourCoordinates, ← atomFactorEquiv_weight m a b c h, AddEquiv.apply_symm_apply]

theorem minimal_atom_presentations_card_eq (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (R T : Finset (AtomCoefficients (generatedSemigroup m a b c) ×
      AtomCoefficients (generatedSemigroup m a b c)))
    (hR : IsAtomPresentation (generatedSemigroup m a b c) R)
    (hT : IsAtomPresentation (generatedSemigroup m a b c) T)
    (iR : ∀ P, P ⊂ R → ¬ IsAtomPresentation (generatedSemigroup m a b c) P)
    (iT : ∀ P, P ⊂ T → ¬ IsAtomPresentation (generatedSemigroup m a b c) P) : R.card = T.card := by
  let e := atomToFour m a b c h
  have hmap := numericPresentation_transport e (atomWeight (generatedSemigroup m a b c))
    (degree ![m,a,b,c]) (atomToFour_weight m a b c h)
  have hr : NumericPresentation (degree ![m,a,b,c]) (mapRelations e R) := (hmap R).mpr hR
  have ht : NumericPresentation (degree ![m,a,b,c]) (mapRelations e T) := (hmap T).mpr hT
  have ir := numeric_minimal_transport e (atomWeight (generatedSemigroup m a b c))
    (degree ![m,a,b,c]) (atomToFour_weight m a b c h) R iR
  have it := numeric_minimal_transport e (atomWeight (generatedSemigroup m a b c))
    (degree ![m,a,b,c]) (atomToFour_weight m a b c h) T iT
  have hc := minimal_numeric_card_eq ![m,a,b,c] (generators_positive m a b c h)
    (mapRelations e R) (mapRelations e T) hr ht ir it
  simpa only [mapRelations_card] using hc

end NSP3.CommonCard

namespace NSP3

/-- Every finite inclusion-minimal actual atom presentation has the intrinsic minimum card. -/
theorem literature_common_cardinality_bridge
    (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (R : Finset (AtomCoefficients (generatedSemigroup m a b c) ×
      AtomCoefficients (generatedSemigroup m a b c)))
    (hR : IsAtomPresentation (generatedSemigroup m a b c) R)
    (hmin : ∀ T, T ⊂ R → ¬ IsAtomPresentation (generatedSemigroup m a b c) T) :
    R.card = intrinsicRho (generatedSemigroup m a b c) := by
  obtain ⟨T,hT,hcard,hTmin⟩ := intrinsicRho_minimal_attained m a b c h
  exact (CommonCard.minimal_atom_presentations_card_eq m a b c h R T hR hT hmin hTmin).trans hcard

theorem literature_minimal_presentation_real_sharp
    (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (R : Finset (AtomCoefficients (generatedSemigroup m a b c) ×
      AtomCoefficients (generatedSemigroup m a b c)))
    (hR : IsAtomPresentation (generatedSemigroup m a b c) R)
    (hmin : ∀ T, T ⊂ R → ¬ IsAtomPresentation (generatedSemigroup m a b c) T) :
    R.card ≤ ⌊(2 : ℝ)+2*Real.sqrt (m : ℝ)⌋₊ := by
  rw [literature_common_cardinality_bridge m a b c h R hR hmin]
  exact intrinsic_rho_real_sharp m a b c h

end NSP3
