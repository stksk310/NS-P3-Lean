import NSP3.CommonCardBridge

namespace NSP3.Sharpness

open NSP3.CommonCard

theorem joined_preserves_isolated {V : Type*} (E : V → V → Prop)
    (R : Finset (V × V)) (u : V)
    (hE : ∀ x y, E x y → (x = u ↔ y = u))
    (hR : ∀ e ∈ R, e.1 ≠ u ∧ e.2 ≠ u)
    {x y : V} (h : _root_.CommonCard.joined E R x y) : x = u ↔ y = u := by
  induction h with
  | rel x y hxy =>
    rcases hxy with he | hr
    · exact hE x y he
    · have hn := hR (x,y) hr
      simp only [Prod.fst,Prod.snd] at hn
      simp [hn.1,hn.2]
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem isolated_requires_degree_edge (g : Fin 4 → ℕ)
    (R : Finset (FourCoeff × FourCoeff)) (hR : NumericPresentation (degree g) R)
    (u v : FourCoeff) (he : degree g u = degree g v) (hne : u ≠ v)
    (hs : ∀ w, BaseEdge g (degree g u) u w → w = u) :
    ∃ e ∈ R, degree g e.1 = degree g u := by
  classical
  let P := degreeSlice g (degree g u) R
  have hc := generated_joined_slice g R (presentation_homogeneous g R hR)
    ((hR u v).mpr he) (degree g u) rfl
  have hex : ∃ e ∈ P, e.1 = u ∨ e.2 = u := by
    by_contra hn
    have hbase : ∀ x y, BaseEdge g (degree g u) x y → (x=u ↔ y=u) := by
      intro x y hb
      constructor
      · intro hx
        subst x
        exact hs y hb
      · intro hy
        subst y
        apply hs x
        refine ⟨hb.2.1,hb.1,?_⟩
        obtain ⟨i,hx,hy⟩ := hb.2.2
        exact ⟨i,hy,hx⟩
    have hp : ∀ e ∈ P, e.1 ≠ u ∧ e.2 ≠ u := by
      intro e heP
      exact ⟨fun hh => hn ⟨e,heP,Or.inl hh⟩,fun hh => hn ⟨e,heP,Or.inr hh⟩⟩
    have hvu := (joined_preserves_isolated (BaseEdge g (degree g u)) P u hbase hp hc).mp rfl
    exact hne hvu.symm
  obtain ⟨e,heP,_⟩ := hex
  exact ⟨e,(Finset.mem_filter.mp heP).1,(Finset.mem_filter.mp heP).2⟩

theorem isolated_degrees_card_le (g : Fin 4 → ℕ) (U : Finset FourCoeff)
    (hi : Set.InjOn (degree g) (U : Set FourCoeff))
    (hv : ∀ u ∈ U, ∃ v, degree g u = degree g v ∧ u ≠ v)
    (hs : ∀ u ∈ U, ∀ v, BaseEdge g (degree g u) u v → v = u)
    (R : Finset (FourCoeff × FourCoeff)) (hR : NumericPresentation (degree g) R) :
    U.card ≤ R.card := by
  classical
  have hsub : U.image (degree g) ⊆ R.image (fun e => degree g e.1) := by
    intro n hn
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨v,he,hne⟩ := hv u hu
    obtain ⟨e,heR,heq⟩ := isolated_requires_degree_edge g R hR u v he hne (hs u hu)
    exact Finset.mem_image.mpr ⟨e,heR,heq⟩
  calc
    U.card = (U.image (degree g)).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ (R.image (fun e => degree g e.1)).card := Finset.card_le_card hsub
    _ ≤ R.card := Finset.card_image_le

theorem isolated_degrees_intrinsic_lower (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (U : Finset FourCoeff)
    (hi : Set.InjOn (degree ![m,a,b,c]) (U : Set FourCoeff))
    (hv : ∀ u ∈ U, ∃ v, degree ![m,a,b,c] u = degree ![m,a,b,c] v ∧ u ≠ v)
    (hs : ∀ u ∈ U, ∀ v, BaseEdge ![m,a,b,c] (degree ![m,a,b,c] u) u v → v = u) :
    U.card ≤ intrinsicRho (generatedSemigroup m a b c) := by
  obtain ⟨R,hR,hcard⟩ := intrinsicRho_attained m a b c h
  let e := atomToFour m a b c h
  have ht := (numericPresentation_transport e (atomWeight (generatedSemigroup m a b c))
    (degree ![m,a,b,c]) (atomToFour_weight m a b c h) R).mpr hR
  have hl := isolated_degrees_card_le ![m,a,b,c] U hi hv hs (mapRelations e R) ht
  rwa [mapRelations_card,hcard] at hl

theorem base_isolated_of_unique_predecessors (g : Fin 4 → ℕ) (u : FourCoeff)
    (hu : ∀ i, 0 < u i → ∀ w,
      degree g (u-Pi.single i 1) = degree g w → w = u-Pi.single i 1)
    (v : FourCoeff) (hb : BaseEdge g (degree g u) u v) : v = u := by
  classical
  obtain ⟨i,hui,hvi⟩ := hb.2.2
  have hurec := subtract_single_reconstruct u i hui
  have hvrec := subtract_single_reconstruct v i hvi
  have he : degree g (u-Pi.single i 1) = degree g (v-Pi.single i 1) := by
    have hdu : degree g u = degree g (u-Pi.single i 1) + g i := by
      conv_lhs => rw [hurec]
      rw [degree_add,degree_single]
    have hdv : degree g v = degree g (v-Pi.single i 1) + g i := by
      conv_lhs => rw [hvrec]
      rw [degree_add,degree_single]
    have hn := hb.2.1
    omega
  have hp := hu i hui (v-Pi.single i 1) he
  calc
    v = (v-Pi.single i 1) + Pi.single i 1 := hvrec
    _ = (u-Pi.single i 1) + Pi.single i 1 := congrArg (fun w => w+Pi.single i 1) hp
    _ = u := hurec.symm

end NSP3.Sharpness
