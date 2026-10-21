import NSP3.SharpnessLowerBound

open NSP3.CommonCard

example (g : Fin 4 → ℕ) (U : Finset FourCoeff)
    (hi : Set.InjOn (degree g) (U : Set FourCoeff))
    (hv : ∀ u ∈ U, ∃ v, degree g u = degree g v ∧ u ≠ v)
    (hs : ∀ u ∈ U, ∀ v, BaseEdge g (degree g u) u v → v = u)
    (R : Finset (FourCoeff × FourCoeff)) (hR : NumericPresentation (degree g) R) :
    U.card ≤ R.card :=
  NSP3.Sharpness.isolated_degrees_card_le g U hi hv hs R hR
