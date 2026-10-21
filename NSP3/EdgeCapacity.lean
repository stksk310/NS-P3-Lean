import Mathlib

namespace NSP3

def edgeLeft {L : ℕ} (i : Fin (L - 1)) : Fin L :=
  Fin.castLE (Nat.sub_le L 1) i

def edgeRight {L : ℕ} (i : Fin (L - 1)) : Fin L :=
  ⟨i.1 + 1, by omega⟩

@[simp] theorem edgeLeft_val {L : ℕ} (i : Fin (L - 1)) : (edgeLeft i).1 = i.1 := rfl

@[simp] theorem edgeRight_val {L : ℕ} (i : Fin (L - 1)) : (edgeRight i).1 = i.1 + 1 := rfl

/-- A mixed-sign path with a common cyclic edge class cannot be too long for its range.
The two families of allowed edge starts are only union-bounded; no disjointness is assumed. -/
theorem cyclicEdgeCapacity {L R h d : ℕ} (c : Fin L → ℕ)
    (hL : 2 ≤ L)
    (hlower : ∀ i, 1 ≤ c i)
    (hupper : ∀ i, c i ≤ R)
    (hinj : Function.Injective c)
    (hh : R + 1 ≤ h)
    (hd : 1 ≤ d)
    (hedge : ∀ i : Fin (L - 1),
      c (edgeRight i) = c (edgeLeft i) + d ∨
      c (edgeLeft i) = c (edgeRight i) + (h - d))
    (hpos : ∃ i : Fin (L - 1), c (edgeRight i) = c (edgeLeft i) + d)
    (hneg : ∃ i : Fin (L - 1), c (edgeLeft i) = c (edgeRight i) + (h - d)) :
    h ≤ 2 * R - L + 1 := by
  classical
  obtain ⟨ip, hip⟩ := hpos
  obtain ⟨ineg, hineg⟩ := hneg
  have hdR : d ≤ R := by
    have := hupper (edgeRight ip)
    omega
  have hdlt : d < h := by omega
  have hhdR : h - d ≤ R := by
    have hs := hupper (edgeLeft ineg)
    have he := hlower (edgeRight ineg)
    omega
  let starts : Finset ℕ := Finset.univ.image (fun i : Fin (L - 1) => c (edgeLeft i))
  let upStarts : Finset ℕ := Finset.Icc 1 (R - d)
  let downStarts : Finset ℕ := Finset.Icc (h - d + 1) R
  have hstartcard : starts.card = L - 1 := by
    dsimp [starts]
    rw [Finset.card_image_iff.mpr]
    · simp
    · intro i _ j _ hij
      apply Fin.ext
      have hc : edgeLeft i = edgeLeft j := hinj hij
      exact congrArg (fun x : Fin L => x.1) hc
  have hsubset : starts ⊆ upStarts ∪ downStarts := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
    rcases hedge i with hup | hdown
    · apply Finset.mem_union_left
      apply Finset.mem_Icc.mpr
      have hlo := hlower (edgeLeft i)
      have hhi := hupper (edgeRight i)
      exact ⟨hlo, by omega⟩
    · apply Finset.mem_union_right
      apply Finset.mem_Icc.mpr
      have hlo := hlower (edgeRight i)
      have hhi := hupper (edgeLeft i)
      exact ⟨by omega, hhi⟩
  have hcsub : starts.card ≤ (upStarts ∪ downStarts).card :=
    Finset.card_le_card hsubset
  have hcunion : (upStarts ∪ downStarts).card ≤ upStarts.card + downStarts.card :=
    Finset.card_union_le _ _
  have hupcard : upStarts.card = R - d := by
    simp [upStarts, Nat.card_Icc, hdR]
  have hdowncard : downStarts.card = R - (h - d) := by
    simp [downStarts, Nat.card_Icc, hhdR]
  have hcount : L - 1 ≤ (R - d) + (R - (h - d)) := by
    calc
      L - 1 = starts.card := hstartcard.symm
      _ ≤ (upStarts ∪ downStarts).card := hcsub
      _ ≤ upStarts.card + downStarts.card := hcunion
      _ = (R - d) + (R - (h - d)) := by rw [hupcard, hdowncard]
  omega

/-- Adjacent values satisfying one common residue equation have a uniform
positive representative modulo the additive order. -/
theorem edgeForm_of_commonResidue {m L R : ℕ} (p A B : ZMod m) (c : Fin L → ℕ)
    (hL : 2 ≤ L) (hlower : ∀ i, 1 ≤ c i) (hupper : ∀ i, c i ≤ R)
    (hinj : Function.Injective c) (hh : R + 1 ≤ addOrderOf p)
    (hres : ∀ i : Fin (L - 1),
      (c (edgeRight i) : ZMod m) * p + A = (c (edgeLeft i) : ZMod m) * p + B)
    (hpos : ∃ i : Fin (L - 1), c (edgeLeft i) < c (edgeRight i))
    (hneg : ∃ i : Fin (L - 1), c (edgeRight i) < c (edgeLeft i)) :
    ∃ d, 1 ≤ d ∧
      (∀ i : Fin (L - 1),
        c (edgeRight i) = c (edgeLeft i) + d ∨
        c (edgeLeft i) = c (edgeRight i) + (addOrderOf p - d)) ∧
      (∃ i : Fin (L - 1), c (edgeRight i) = c (edgeLeft i) + d) ∧
      (∃ i : Fin (L - 1),
        c (edgeLeft i) = c (edgeRight i) + (addOrderOf p - d)) := by
  obtain ⟨ip, hip⟩ := hpos
  let d := c (edgeRight ip) - c (edgeLeft ip)
  have hd : 1 ≤ d := by dsimp [d]; omega
  have hdlt : d < addOrderOf p := by
    have hu := hupper (edgeRight ip)
    dsimp [d]
    omega
  have hdp : (d : ZMod m) * p + A = B := by
    have hr := hres ip
    have heq : c (edgeLeft ip) + d = c (edgeRight ip) := by dsimp [d]; omega
    rw [← heq] at hr
    push_cast at hr
    linear_combination hr
  have hedge : ∀ i : Fin (L - 1),
      c (edgeRight i) = c (edgeLeft i) + d ∨
      c (edgeLeft i) = c (edgeRight i) + (addOrderOf p - d) := by
    intro i
    have hne : c (edgeLeft i) ≠ c (edgeRight i) := by
      intro heq
      have := hinj heq
      have hv := congrArg Fin.val this
      simp [edgeLeft, edgeRight] at hv
    rcases lt_or_gt_of_ne hne with hup | hdown
    · left
      let z := c (edgeRight i) - c (edgeLeft i)
      have hzlt : z < addOrderOf p := by
        have hu := hupper (edgeRight i)
        dsimp [z]
        omega
      have hzp : (z : ZMod m) * p = (d : ZMod m) * p := by
        have hr := hres i
        have heq : c (edgeLeft i) + z = c (edgeRight i) := by dsimp [z]; omega
        rw [← heq] at hr
        push_cast at hr
        linear_combination hr - hdp
      have hzd : z = d := by
        apply nsmul_injOn_Iio_addOrderOf (x := p) hzlt hdlt
        simpa [nsmul_eq_mul] using hzp
      dsimp [z] at hzd
      omega
    · right
      let z := c (edgeLeft i) - c (edgeRight i)
      have hz : 1 ≤ z := by dsimp [z]; omega
      have hzlt : z < addOrderOf p := by
        have hu := hupper (edgeLeft i)
        dsimp [z]
        omega
      have hsumzero : (d + z) • p = 0 := by
        have hr := hres i
        have heq : c (edgeRight i) + z = c (edgeLeft i) := by dsimp [z]; omega
        rw [← heq] at hr
        push_cast at hr
        have hzrel : A = (z : ZMod m) * p + B := by
          linear_combination hr
        rw [nsmul_eq_mul]
        push_cast
        linear_combination hdp - hzrel
      have hdvd : addOrderOf p ∣ d + z :=
        addOrderOf_dvd_iff_nsmul_eq_zero.mpr hsumzero
      obtain ⟨k, hk⟩ := hdvd
      have hordpos : 0 < addOrderOf p := by omega
      have hsumlt : d + z < 2 * addOrderOf p := by omega
      have hklt : k < 2 := by
        apply (Nat.mul_lt_mul_left hordpos).mp
        rw [← hk]
        omega
      have hkpos : 0 < k := by
        by_contra hnot
        have hkzero : k = 0 := Nat.eq_zero_of_not_pos hnot
        rw [hkzero] at hk
        simp at hk
        omega
      have hkone : k = 1 := by omega
      have hsum : d + z = addOrderOf p := by
        rw [hkone] at hk
        simpa using hk
      change c (edgeLeft i) = c (edgeRight i) + (addOrderOf p - d)
      dsimp [z] at hsum
      omega
  refine ⟨d, hd, hedge, ?_, ?_⟩
  · exact ⟨ip, by dsimp [d]; omega⟩
  · obtain ⟨ineg, hineg⟩ := hneg
    rcases hedge ineg with hup | hdown
    · omega
    · exact ⟨ineg, hdown⟩

/-- Span bound for a path whose adjacent edges are all positive and at least `D`. -/
theorem allPositiveEdgeSpan {L R D : ℕ} (c : Fin L → ℕ)
    (hL : 2 ≤ L)
    (hlower : ∀ i, 1 ≤ c i)
    (hupper : ∀ i, c i ≤ R)
    (hstep : ∀ i : Fin (L - 1),
      c (edgeLeft i) < c (edgeRight i) ∧
      D ≤ c (edgeRight i) - c (edgeLeft i)) :
    D * (L - 1) ≤ R - 1 := by
  let i0 : Fin L := ⟨0, by omega⟩
  have hacc : ∀ k : ℕ, (hk : k < L) →
      D * k + c i0 ≤ c ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; simpa [i0]
    | succ k ih =>
        intro hk
        have hk0 : k < L := by omega
        have hki : k < L - 1 := by omega
        have hprev := ih hk0
        have hs := hstep ⟨k, hki⟩
        change c ⟨k, hk0⟩ < c ⟨k + 1, hk⟩ ∧
          D ≤ c ⟨k + 1, hk⟩ - c ⟨k, hk0⟩ at hs
        rw [Nat.mul_succ]
        omega
  have hlast := hacc (L - 1) (by omega)
  have hlo := hlower i0
  have hhi := hupper ⟨L - 1, by omega⟩
  omega

/-- Span bound for a path whose adjacent edges are all negative with magnitude at least `D`. -/
theorem allNegativeEdgeSpan {L R D : ℕ} (c : Fin L → ℕ)
    (hL : 2 ≤ L)
    (hlower : ∀ i, 1 ≤ c i)
    (hupper : ∀ i, c i ≤ R)
    (hstep : ∀ i : Fin (L - 1),
      c (edgeRight i) < c (edgeLeft i) ∧
      D ≤ c (edgeLeft i) - c (edgeRight i)) :
    D * (L - 1) ≤ R - 1 := by
  let i0 : Fin L := ⟨0, by omega⟩
  have hacc : ∀ k : ℕ, (hk : k < L) →
      D * k + c ⟨k, hk⟩ ≤ c i0 := by
    intro k
    induction k with
    | zero => intro hk; simpa [i0]
    | succ k ih =>
        intro hk
        have hk0 : k < L := by omega
        have hki : k < L - 1 := by omega
        have hprev := ih hk0
        have hs := hstep ⟨k, hki⟩
        change c ⟨k + 1, hk⟩ < c ⟨k, hk0⟩ ∧
          D ≤ c ⟨k, hk0⟩ - c ⟨k + 1, hk⟩ at hs
        rw [Nat.mul_succ]
        omega
  have hlast := hacc (L - 1) (by omega)
  have hlo := hlower ⟨L - 1, by omega⟩
  have hhi := hupper i0
  omega

end NSP3
