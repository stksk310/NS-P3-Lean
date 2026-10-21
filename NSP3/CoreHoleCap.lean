import NSP3.CoreHole
import NSP3.SimplexPolynomial

namespace NSP3

noncomputable def coreHoleHeight (S : CyclicStaircase) : ℕ :=
  (pair13Count S.D + pair23Count S.D + 2 - pair12Count S.D) / 2

def largeHoleCap (t : ℕ) : ℕ := Nat.choose ((t + 2) / 2) 3

private theorem simplexCard_diag (h : ℕ) :
    simplexCard (h - 1) (h - 1) = Nat.choose h 3 := by
  cases h with
  | zero => simp [simplexCard]
  | succ n =>
      have hs := six_mul_simplexCard n n (by omega)
      have hc := Nat.descFactorial_eq_factorial_mul_choose (n + 1) 3
      norm_num [Nat.descFactorial] at hc
      simp only [Nat.add_sub_cancel] at ⊢
      apply Nat.eq_of_mul_eq_mul_left (n := 6) (by norm_num)
      calc
        6 * simplexCard n n = n * (n - 1) * (3 * n - 2 * n + 1) := hs
        _ = n * (n - 1) * (n + 1) := by congr 1 <;> omega
        _ = (n - 1) * (n * (n + 1)) := by ring
        _ = 6 * Nat.choose (n + 1) 3 := hc

private def positiveToOrdered (h X Y Z : ℕ) (hX : 0 < X) (hY : 0 < Y)
    (hZ : 0 < Z) (hsum : X + Y + Z ≤ h) :
    OrderedSimplexSource (h - 1) (h - 1) :=
  let u : Fin (h - 1 - 1) := ⟨Y + Z - 2, by omega⟩
  let a : Fin (u.1 + 1) := ⟨Y - 1, by dsimp [u]; omega⟩
  let b : Fin ((h - 1) - (u.1 + 1)) := ⟨X - 1, by dsimp [u]; omega⟩
  ⟨u, a, b⟩

private theorem coreHoleTranslated_bounds (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (p : {p : Point3 // p ∈ coreHoleFinset S g}) :
    0 < p.1.x - g.x + 1 ∧ 0 < p.1.y - g.y + 1 ∧
      0 < p.1.z - g.z + 1 ∧
      (p.1.x - g.x + 1) + (p.1.y - g.y + 1) + (p.1.z - g.z + 1) ≤
        coreHoleHeight S := by
  let X := p.1.x - g.x + 1
  let Y := p.1.y - g.y + 1
  let Z := p.1.z - g.z + 1
  have hp := (mem_coreHoleFinset S g p.1).mp p.2
  have hterm := pair12_terminal_return_capacity_ordered S hg hfull hord
  have hxy := hp.1.2.2.2.1
  have hxz := hp.1.2.2.2.2.1
  have hyz := hp.1.2.2.2.2.2
  rcases hp.2 with ⟨hgx, hgy, hgz⟩
  have hsum2 : 2 * (X + Y + Z) ≤
      pair13Count S.D + pair23Count S.D + 2 - pair12Count S.D := by
    dsimp [X, Y, Z]
    omega
  have hsum : X + Y + Z ≤ coreHoleHeight S := by
    unfold coreHoleHeight
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 2)]
    simpa [Nat.mul_comm] using hsum2
  have hX : 0 < X := by dsimp [X]; omega
  have hY : 0 < Y := by dsimp [Y]; omega
  have hZ : 0 < Z := by dsimp [Z]; omega
  exact ⟨hX, hY, hZ, hsum⟩

private noncomputable def coreHoleToSimplex (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (p : {p : Point3 // p ∈ coreHoleFinset S g}) :
    OrderedSimplexSource (coreHoleHeight S - 1) (coreHoleHeight S - 1) :=
  positiveToOrdered (coreHoleHeight S)
    (p.1.x - g.x + 1) (p.1.y - g.y + 1) (p.1.z - g.z + 1)
    (coreHoleTranslated_bounds S hg hfull hord p).1
    (coreHoleTranslated_bounds S hg hfull hord p).2.1
    (coreHoleTranslated_bounds S hg hfull hord p).2.2.1
    (coreHoleTranslated_bounds S hg hfull hord p).2.2.2

private theorem coreHoleToSimplex_point (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) (p : {p : Point3 // p ∈ coreHoleFinset S g}) :
    orderedSimplexPoint (coreHoleHeight S - 1) (coreHoleHeight S - 1)
      (coreHoleToSimplex S hg hfull hord p) =
        Point3.mk (p.1.x - g.x + 1) (p.1.y - g.y + 1) (p.1.z - g.z + 1) := by
  have hp := (mem_coreHoleFinset S g p.1).mp p.2
  rcases hp.2 with ⟨hx, hy, hz⟩
  apply Point3.ext <;>
    simp [coreHoleToSimplex, positiveToOrdered, orderedSimplexPoint] <;> omega

private theorem coreHoleToSimplex_injective (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) :
    Function.Injective (coreHoleToSimplex S hg hfull hord) := by
  intro p q heq
  have hp := (mem_coreHoleFinset S g p.1).mp p.2
  have hq := (mem_coreHoleFinset S g q.1).mp q.2
  rcases hp.2 with ⟨hpx, hpy, hpz⟩
  rcases hq.2 with ⟨hqx, hqy, hqz⟩
  have heq' := congrArg
    (orderedSimplexPoint (coreHoleHeight S - 1) (coreHoleHeight S - 1)) heq
  rw [coreHoleToSimplex_point S hg hfull hord p,
    coreHoleToSimplex_point S hg hfull hord q] at heq'
  have hx := congrArg Point3.x heq'
  have hy := congrArg Point3.y heq'
  have hz := congrArg Point3.z heq'
  apply Subtype.ext
  apply Point3.ext <;> simp only [Point3.x, Point3.y, Point3.z] at hx hy hz ⊢ <;> omega

theorem coreHole_card_le_choose_height (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) :
    (coreHoleFinset S g).card ≤ Nat.choose (coreHoleHeight S) 3 := by
  let f := coreHoleToSimplex S hg hfull hord
  have hf := Fintype.card_le_of_injective f (coreHoleToSimplex_injective S hg hfull hord)
  rw [card_orderedSimplexSource, simplexCard_diag] at hf
  simpa using hf

theorem coreHole_card_le_largeHoleCap (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hord : PairCountsOrdered S) :
    (coreHoleFinset S g).card ≤ largeHoleCap (pair23Count S.D) := by
  have h := coreHole_card_le_choose_height S hg hfull hord
  have hsr := hord.2
  have hh : coreHoleHeight S ≤ (pair23Count S.D + 2) / 2 := by
    unfold coreHoleHeight
    apply Nat.div_le_div_right
    omega
  exact h.trans (Nat.choose_le_choose 3 hh)

end NSP3
