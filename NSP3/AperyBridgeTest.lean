import NSP3.AperyBridge

namespace NSP3

example (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    Nat.card {q : Point3 // MinimalComplement (aperyStandardSet m a b c hm hgcd) q} ≤
      2 + Nat.sqrt (4*m) :=
  apery_boundary_card_sharp m a b c hm hgcd

example (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    Nat.card {q : Point3 // MinimalComplement (aperyStandardSet m a b c hm hgcd) q} ≤
      ⌊(2 : ℝ) + 2 * Real.sqrt (m : ℝ)⌋₊ :=
  apery_boundary_card_real_sharp m a b c hm hgcd

-- Composite modulus: none of 6,10,15 is a unit modulo 30.
example : Function.Surjective (residueOf (6 : ZMod 30) (10 : ZMod 30) (15 : ZMod 30)) :=
  apery_residue_surjective 30 6 10 15 (by norm_num) (by norm_num)

-- The one-residue case with repeated positive weights is not excluded.
example : (aperyStandardSet 1 7 7 7 (by norm_num) (by norm_num)).card = 1 :=
  aperyStandardSet_card 1 7 7 7 (by norm_num) (by norm_num)

-- A genuinely equal-weight tie is ordered by x before y.
example : aperyWeight 7 7 7 ⟨0,1,0⟩ = aperyWeight 7 7 7 ⟨1,0,0⟩ := by
  norm_num [aperyWeight]

example : aperyKey 7 7 7 ⟨0,1,0⟩ < aperyKey 7 7 7 ⟨1,0,0⟩ := by
  decide

-- Zero coordinates, even zero weights in the stronger helper, remain allowed.
example : AperyCanonical 1 0 0 0 ⟨0,0,0⟩ := by
  intro u _
  exact bot_le

end NSP3
