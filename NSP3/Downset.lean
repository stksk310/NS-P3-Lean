import NSP3.Basic

namespace NSP3

/-- Coordinatewise down-closure of a finite set of lattice points. -/
def IsDownset (D : Finset Point3) : Prop :=
  ∀ ⦃a b : Point3⦄, a ≤ b → b ∈ D → a ∈ D

theorem IsDownset.mem_of_le {D : Finset Point3} (hD : IsDownset D)
    {a b : Point3} (hab : a ≤ b) (hb : b ∈ D) : a ∈ D :=
  hD hab hb

end NSP3
