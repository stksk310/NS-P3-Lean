import NSP3.AperyConstruction
import NSP3.BoundaryReal

namespace NSP3

/-- All frozen staircase fields are constructed from the numeric input. -/
noncomputable def aperyCyclicStaircase (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) : CyclicStaircase where
  m := m
  hm := hm
  D := aperyStandardSet m a b c hm hgcd
  down_closed := aperyStandardSet_downset m a b c hm hgcd
  p1 := (a : ZMod m)
  p2 := (b : ZMod m)
  p3 := (c : ZMod m)
  residueEquiv := aperyResidueEquiv m a b c hm hgcd
  residueEquiv_spec := aperyResidueEquiv_spec m a b c hm hgcd

theorem aperyStandardSet_card (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    (aperyStandardSet m a b c hm hgcd).card = m :=
  (aperyCyclicStaircase m a b c hm hgcd).card_D

theorem aperyCyclicStaircase_weight_min (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    {q u : Point3} (hq : q ∈ (aperyCyclicStaircase m a b c hm hgcd).D)
    (hr : (aperyCyclicStaircase m a b c hm hgcd).residue u =
      (aperyCyclicStaircase m a b c hm hgcd).residue q) :
    aperyWeight a b c q ≤ aperyWeight a b c u :=
  aperyCanonical_weight_min m a b c ((mem_aperyStandardSet m a b c hm hgcd q).mp hq) hr

/-- Cardinality of the actual constructed boundary, not a presentation count. -/
theorem apery_boundary_card_sharp (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    Nat.card {q : Point3 // MinimalComplement (aperyStandardSet m a b c hm hgcd) q} ≤
      2 + Nat.sqrt (4*m) :=
  cyclicStaircase_boundary_card_sharp (aperyCyclicStaircase m a b c hm hgcd)

theorem apery_boundary_card_real_sharp (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    Nat.card {q : Point3 // MinimalComplement (aperyStandardSet m a b c hm hgcd) q} ≤
      ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ :=
  cyclicStaircase_boundary_card_real_sharp (aperyCyclicStaircase m a b c hm hgcd)

end NSP3
