import NSP3.PresentationGeometry

namespace NSP3
-- Catches replacing actual border coverage by an extra downset/reduction assumption.
example (D : Finset Point3) (p : Point3) (hp : p ∉ D) :
    ∃ b : Point3, MinimalComplement D b ∧ b ≤ p :=
  presentation_border_exists_le D p hp

-- Catches a numeric factor map that forgets a generator or additive context.
example (m a b c : ℕ) (u v : ℕ × Point3) :
    (u+v).1*m+aperyWeight a b c (u+v).2 =
      (u.1*m+aperyWeight a b c u.2)+(v.1*m+aperyWeight a b c v.2) :=
  factorWeight_add m a b c u v
end NSP3
