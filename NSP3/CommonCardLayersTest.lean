import NSP3.CommonCardLayers
namespace NSP3.CommonCard
example (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i)
    (R T : Finset (FourCoeff × FourCoeff))
    (hR : NumericPresentation (degree g) R) (hT : NumericPresentation (degree g) T)
    (iR : ∀ P, P ⊂ R → ¬ NumericPresentation (degree g) P)
    (iT : ∀ P, P ⊂ T → ¬ NumericPresentation (degree g) P) : R.card = T.card :=
  minimal_numeric_card_eq g hg R T hR hT iR iT

example {A : Type*} [Add A] [DecidableEq A] (w : A → ℕ)
    (R : Finset (A × A)) (hR : NumericPresentation w R)
    (hmin : ∀ P, P ⊂ R → ¬ NumericPresentation w P) (u : A) : (u,u) ∉ R := by
  intro he
  exact minimal_edge_not_generated w R hR hmin (u,u) he (.refl u)
end NSP3.CommonCard
