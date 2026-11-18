import NSP3.SharpnessLowerBound

namespace NSP3.V03
open NSP3.CommonCard
open NSP3.Sharpness

/-- Isolated vertices count separately even when several have the same degree. -/
theorem isolated_vertices_card_le_edges {V : Type*} [DecidableEq V]
    (E : V→V→Prop) (U : Finset V) (w : V→V)
    (hw : ∀ u∈U, w u∉U)
    (hE : ∀ u∈U, ∀ x y, E x y → (x=u ↔ y=u))
    (R : Finset (V×V))
    (hj : ∀ u∈U, _root_.CommonCard.joined E R u (w u)) : U.card≤R.card := by
  classical
  let T := U.image (fun u => (u,w u))
  have hcard : T.card=U.card := Finset.card_image_of_injective U
    (by intro u v he; exact congrArg Prod.fst he)
  have hi : ∀ e∈T, ¬ _root_.CommonCard.joined E (T.erase e) e.1 e.2 := by
    intro e he hjoin
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
    have hother : ∀ e∈T.erase (u,w u), e.1≠u ∧ e.2≠u := by
      intro e he
      obtain ⟨hne,he⟩ := Finset.mem_erase.mp he
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp he
      refine ⟨?_,?_⟩
      · intro h
        exact hne (by simp only [Prod.mk.injEq]; exact ⟨h,congrArg w h⟩)
      · intro h
        change w v=u at h
        apply hw v hv
        change w v∈U
        rw [h]
        exact hu
    have heq := (joined_preserves_isolated E (T.erase (u,w u)) u (hE u hu)
      hother hjoin).mp rfl
    change w u=u at heq
    apply hw u hu
    rw [heq]
    exact hu
  have hspan : _root_.CommonCard.edgeSpan E T≤_root_.CommonCard.edgeSpan E R := by
    apply Submodule.span_le.mpr
    rintro _ ⟨e,he,rfl⟩
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp he
    exact _root_.CommonCard.edgeVector_mem_span_of_joined E R (hj u hu)
  letI : Module.Finite ℚ (_root_.CommonCard.edgeSpan E R) :=
    Module.Finite.span_of_finite ℚ (R.finite_toSet.image (_root_.CommonCard.edgeVector E))
  have hrankT : Module.finrank ℚ (_root_.CommonCard.edgeSpan E T)=T.card := by
    rw [_root_.CommonCard.edgeSpan_eq_span_range]
    simpa using finrank_span_eq_card (_root_.CommonCard.edgeVectors_linearIndependent E T hi)
  have hrankR : Module.finrank ℚ (_root_.CommonCard.edgeSpan E R)≤R.card := by
    rw [_root_.CommonCard.edgeSpan_eq_span_range]
    simpa only [Set.finrank,Fintype.card_coe] using finrank_range_le_card (R := ℚ)
      (fun e : R => _root_.CommonCard.edgeVector E e.val)
  have hmono := Submodule.finrank_mono hspan
  omega

private def anyBaseEdge (g : Fin 4→ℕ) (u v : FourCoeff) : Prop :=
  BaseEdge g (degree g u) u v

private theorem generated_joined_any (g : Fin 4→ℕ)
    (R : Finset (FourCoeff×FourCoeff)) (hR : NumericPresentation (degree g) R)
    {u v : FourCoeff} (h : GeneratedAddRel R u v) :
    _root_.CommonCard.joined (anyBaseEdge g) R u v := by
  induction h with
  | edge he => exact .rel _ _ (Or.inr he)
  | refl u => exact .refl u
  | symm _ ih => exact .symm _ _ ih
  | trans _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂
  | context h d ih =>
    by_cases hd : d=0
    · subst d
      simpa using ih
    have hex : ∃ i, 0 < d i := by
      by_contra hn
      apply hd
      funext i
      change d i=0
      have hni : ¬ 0 < d i := fun h => hn ⟨i,h⟩
      omega
    obtain ⟨i,hi⟩ := hex
    have he := (hR _ _).mp h
    apply Relation.EqvGen.rel
    left
    refine ⟨rfl,?_,i,?_,?_⟩
    · simp only [degree_add,he]
    · simp only [Pi.add_apply]
      omega
    · simp only [Pi.add_apply]
      omega

theorem multi_isolated_card_le (g : Fin 4→ℕ) (U : Finset FourCoeff)
    (hv : ∀ u∈U, ∃ v, degree g u=degree g v ∧ v∉U)
    (hs : ∀ u∈U, ∀ v, BaseEdge g (degree g u) u v → v=u)
    (R : Finset (FourCoeff×FourCoeff)) (hR : NumericPresentation (degree g) R) :
    U.card≤R.card := by
  classical
  let w (u : FourCoeff) := if hu : u∈U then Classical.choose (hv u hu) else u
  have hw (u : FourCoeff) (hu : u∈U) : degree g u=degree g (w u) ∧ w u∉U := by
    dsimp [w]
    rw [dif_pos hu]
    exact Classical.choose_spec (hv u hu)
  apply isolated_vertices_card_le_edges (anyBaseEdge g) U w
    (fun u hu => (hw u hu).2) ?_ R ?_
  · intro u hu x y hxy
    constructor
    · intro hx
      subst x
      exact hs u hu y hxy
    · intro hy
      subst y
      apply hs u hu x
      exact ⟨rfl,hxy.2.1.symm,by
        obtain ⟨i,hx,hy⟩ := hxy.2.2
        exact ⟨i,hy,hx⟩⟩
  · intro u hu
    exact generated_joined_any g R hR ((hR _ _).mpr (hw u hu).1)

theorem multi_isolated_intrinsic_lower (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (U : Finset FourCoeff)
    (hv : ∀ u∈U, ∃ v, degree ![m,a,b,c] u=degree ![m,a,b,c] v ∧ v∉U)
    (hs : ∀ u∈U, ∀ v, BaseEdge ![m,a,b,c] (degree ![m,a,b,c] u) u v → v=u) :
    U.card ≤ intrinsicRho (generatedSemigroup m a b c) := by
  obtain ⟨R,hR,hcard⟩ := intrinsicRho_attained m a b c h
  let e := atomToFour m a b c h
  have ht := (numericPresentation_transport e (atomWeight (generatedSemigroup m a b c))
    (degree ![m,a,b,c]) (atomToFour_weight m a b c h) R).mpr hR
  have hl := multi_isolated_card_le ![m,a,b,c] U hv hs (mapRelations e R) ht
  rwa [mapRelations_card,hcard] at hl

end NSP3.V03
