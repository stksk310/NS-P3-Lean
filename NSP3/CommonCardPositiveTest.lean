import NSP3.CommonCardPositive

namespace NSP3.CommonCard

example (g : Fin 4 → ℕ) (u v : FourCoeff) :
    degree g (u + v) = degree g u + degree g v := degree_add g u v

example (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i) (u : FourCoeff) :
    degree g u = 0 ↔ u = 0 := degree_eq_zero_iff g hg u

example (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i) (n : ℕ) :
    Finite {u : FourCoeff // degree g u = n} := fiber_finite_positive g hg n

example (g : Fin 4 → ℕ) (hg : ∀ i, 0 < g i) (u v : FourCoeff)
    (he : degree g u = degree g v) (hs : ∃ i, 0 < u i ∧ 0 < v i) :
    ∃ i u' v', u = u' + Pi.single i 1 ∧ v = v' + Pi.single i 1 ∧
      degree g u' = degree g v' ∧ degree g u' < degree g u :=
  support_edge_strict_lower g hg u v he hs

example (u v d : FourCoeff) (hd : d ≠ 0) :
    ∃ i, 0 < (u + d) i ∧ 0 < (v + d) i := context_common_support u v d hd

example (m a b c : ℕ) (u : Fact4) :
    degree ![m,a,b,c] (fourCoordinates u) = factorWeight m a b c u :=
  degree_fourCoordinates m a b c u

example (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    ∀ i : Fin 4, 0 < (![m,a,b,c] : Fin 4 → ℕ) i := generators_positive m a b c h

end NSP3.CommonCard
