import NSP3.CommonCardRelativeGraph

namespace CommonCard

-- Typed contract: arbitrary directed edges, with no loop or orientation restrictions.
example {V : Type*} [DecidableEq V] (E : V → V → Prop)
    (R T : Finset (V × V))
    (hR : ∀ x y, joined E R x y)
    (hT : ∀ x y, joined E T x y)
    (iR : ∀ e ∈ R, ¬ joined E (R.erase e) e.1 e.2)
    (iT : ∀ e ∈ T, ¬ joined E (T.erase e) e.1 e.2) :
    R.card = T.card :=
  relative_card_eq E R T hR hT iR iT

end CommonCard

namespace CommonCard
example {V : Type*} [DecidableEq V] (E : V → V → Prop)
    (R T : Finset (V × V))
    (hR : ∀ e ∈ T, joined E R e.1 e.2)
    (hT : ∀ e ∈ R, joined E T e.1 e.2)
    (iR : ∀ e ∈ R, ¬ joined E (R.erase e) e.1 e.2)
    (iT : ∀ e ∈ T, ¬ joined E (T.erase e) e.1 e.2) :
    R.card = T.card :=
  relative_card_eq_of_mutual E R T hR hT iR iT
end CommonCard
