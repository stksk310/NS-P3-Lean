import NSP3.PlaneResources

namespace NSP3

private theorem pair12Boundary_x_injective (S : CyclicStaircase) :
    Function.Injective (fun b : Pair12Boundary S => b.1.x) := by
  intro b c h
  apply Subtype.ext
  exact pair12_eq_of_x_eq S.down_closed
    (mem_pair12Boundaries.mpr b.2) (mem_pair12Boundaries.mpr c.2) h

private theorem pair13Boundary_x_injective (S : CyclicStaircase) :
    Function.Injective (fun b : Pair13Boundary S => b.1.x) := by
  intro b c h
  apply Subtype.ext
  exact pair13_eq_of_x_eq S.down_closed
    (mem_pair13Boundaries.mpr b.2) (mem_pair13Boundaries.mpr c.2) h

private theorem pair23Boundary_y_injective (S : CyclicStaircase) :
    Function.Injective (fun b : Pair23Boundary S => b.1.y) := by
  intro b c h
  apply Subtype.ext
  exact pair23_eq_of_y_eq S.down_closed
    (mem_pair23Boundaries.mpr b.2) (mem_pair23Boundaries.mpr c.2) h

noncomputable instance pair12BoundaryLinearOrder (S : CyclicStaircase) :
    LinearOrder (Pair12Boundary S) :=
  LinearOrder.lift' (fun b : Pair12Boundary S => b.1.x)
    (pair12Boundary_x_injective S)

noncomputable instance pair13BoundaryLinearOrder (S : CyclicStaircase) :
    LinearOrder (Pair13Boundary S) :=
  LinearOrder.lift' (fun b : Pair13Boundary S => b.1.x)
    (pair13Boundary_x_injective S)

noncomputable instance pair23BoundaryLinearOrder (S : CyclicStaircase) :
    LinearOrder (Pair23Boundary S) :=
  LinearOrder.lift' (fun b : Pair23Boundary S => b.1.y)
    (pair23Boundary_y_injective S)

/-- Zero-based enumeration of Pair12 boundaries by increasing `x`.
Index `i` corresponds canonically to the one-based diagonal point `(i+1,q-i,0)`. -/
noncomputable def orderedPair12Boundary (S : CyclicStaircase) :
    Fin (pair12Count S.D) → Pair12Boundary S :=
  Fintype.orderIsoFinOfCardEq (Pair12Boundary S) (card_pair12Boundary S)

/-- Zero-based enumeration of Pair13 boundaries by increasing `x`. -/
noncomputable def orderedPair13Boundary (S : CyclicStaircase) :
    Fin (pair13Count S.D) → Pair13Boundary S :=
  Fintype.orderIsoFinOfCardEq (Pair13Boundary S) (card_pair13Boundary S)

/-- Zero-based enumeration of Pair23 boundaries by increasing `y`. -/
noncomputable def orderedPair23Boundary (S : CyclicStaircase) :
    Fin (pair23Count S.D) → Pair23Boundary S :=
  Fintype.orderIsoFinOfCardEq (Pair23Boundary S) (card_pair23Boundary S)

theorem orderedPair12Boundary_x_strictMono (S : CyclicStaircase) :
    StrictMono (fun i => (orderedPair12Boundary S i).1.x) := by
  intro i j hij
  have h := (Fintype.orderIsoFinOfCardEq (Pair12Boundary S)
    (card_pair12Boundary S)).strictMono hij
  change (orderedPair12Boundary S i).1.x < (orderedPair12Boundary S j).1.x at h
  exact h

theorem orderedPair13Boundary_x_strictMono (S : CyclicStaircase) :
    StrictMono (fun i => (orderedPair13Boundary S i).1.x) := by
  intro i j hij
  have h := (Fintype.orderIsoFinOfCardEq (Pair13Boundary S)
    (card_pair13Boundary S)).strictMono hij
  change (orderedPair13Boundary S i).1.x < (orderedPair13Boundary S j).1.x at h
  exact h

theorem orderedPair23Boundary_y_strictMono (S : CyclicStaircase) :
    StrictMono (fun i => (orderedPair23Boundary S i).1.y) := by
  intro i j hij
  have h := (Fintype.orderIsoFinOfCardEq (Pair23Boundary S)
    (card_pair23Boundary S)).strictMono hij
  change (orderedPair23Boundary S i).1.y < (orderedPair23Boundary S j).1.y at h
  exact h

theorem orderedPair12Boundary_y_strictAnti (S : CyclicStaircase) :
    StrictAnti (fun i => (orderedPair12Boundary S i).1.y) := by
  intro i j hij
  exact pair12_y_lt_of_x_lt S.down_closed
    (mem_pair12Boundaries.mpr (orderedPair12Boundary S i).2)
    (mem_pair12Boundaries.mpr (orderedPair12Boundary S j).2)
    (orderedPair12Boundary_x_strictMono S hij)

theorem orderedPair13Boundary_z_strictAnti (S : CyclicStaircase) :
    StrictAnti (fun i => (orderedPair13Boundary S i).1.z) := by
  intro i j hij
  exact pair13_z_lt_of_x_lt S.down_closed
    (mem_pair13Boundaries.mpr (orderedPair13Boundary S i).2)
    (mem_pair13Boundaries.mpr (orderedPair13Boundary S j).2)
    (orderedPair13Boundary_x_strictMono S hij)

theorem orderedPair23Boundary_z_strictAnti (S : CyclicStaircase) :
    StrictAnti (fun i => (orderedPair23Boundary S i).1.z) := by
  intro i j hij
  exact pair23_z_lt_of_y_lt S.down_closed
    (mem_pair23Boundaries.mpr (orderedPair23Boundary S i).2)
    (mem_pair23Boundaries.mpr (orderedPair23Boundary S j).2)
    (orderedPair23Boundary_y_strictMono S hij)

private theorem fin_strictMono_succ_le {n : ℕ} (f : Fin n → ℕ)
    (hf : StrictMono f) (hpos : ∀ i, 0 < f i) (i : Fin n) : i.1 + 1 ≤ f i := by
  have aux : ∀ k : ℕ, (hk : k < n) → k + 1 ≤ f ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact hpos ⟨0, hk⟩
    | succ k ih =>
        intro hk
        have hk' : k < n := by omega
        have hlt : f ⟨k, hk'⟩ < f ⟨k + 1, hk⟩ := hf (by simp)
        have hprev := ih hk'
        omega
  exact aux i.1 i.2

private theorem fin_strictAnti_count_sub_le {n : ℕ} (f : Fin n → ℕ)
    (hf : StrictAnti f) (hpos : ∀ i, 0 < f i) (i : Fin n) : n - i.1 ≤ f i := by
  let g : Fin n → ℕ := fun j => f j.rev
  have hg : StrictMono g := by
    intro a b hab
    exact hf (Fin.rev_strictAnti hab)
  have hgpos : ∀ j, 0 < g j := fun j => hpos j.rev
  have h := fin_strictMono_succ_le g hg hgpos i.rev
  simp [g] at h
  omega

theorem orderedPair12Boundary_x_baseline (S : CyclicStaircase)
    (i : Fin (pair12Count S.D)) : i.1 + 1 ≤ (orderedPair12Boundary S i).1.x :=
  fin_strictMono_succ_le _ (orderedPair12Boundary_x_strictMono S)
    (fun j => (orderedPair12Boundary S j).2.2.1) i

theorem orderedPair12Boundary_y_baseline (S : CyclicStaircase)
    (i : Fin (pair12Count S.D)) :
    pair12Count S.D - i.1 ≤ (orderedPair12Boundary S i).1.y :=
  fin_strictAnti_count_sub_le _ (orderedPair12Boundary_y_strictAnti S)
    (fun j => (orderedPair12Boundary S j).2.2.2.1) i

theorem orderedPair13Boundary_x_baseline (S : CyclicStaircase)
    (i : Fin (pair13Count S.D)) : i.1 + 1 ≤ (orderedPair13Boundary S i).1.x :=
  fin_strictMono_succ_le _ (orderedPair13Boundary_x_strictMono S)
    (fun j => (orderedPair13Boundary S j).2.2.1) i

theorem orderedPair13Boundary_z_baseline (S : CyclicStaircase)
    (i : Fin (pair13Count S.D)) :
    pair13Count S.D - i.1 ≤ (orderedPair13Boundary S i).1.z :=
  fin_strictAnti_count_sub_le _ (orderedPair13Boundary_z_strictAnti S)
    (fun j => (orderedPair13Boundary S j).2.2.2.2) i

theorem orderedPair23Boundary_y_baseline (S : CyclicStaircase)
    (i : Fin (pair23Count S.D)) : i.1 + 1 ≤ (orderedPair23Boundary S i).1.y :=
  fin_strictMono_succ_le _ (orderedPair23Boundary_y_strictMono S)
    (fun j => (orderedPair23Boundary S j).2.2.2.1) i

theorem orderedPair23Boundary_z_baseline (S : CyclicStaircase)
    (i : Fin (pair23Count S.D)) :
    pair23Count S.D - i.1 ≤ (orderedPair23Boundary S i).1.z :=
  fin_strictAnti_count_sub_le _ (orderedPair23Boundary_z_strictAnti S)
    (fun j => (orderedPair23Boundary S j).2.2.2.2) i

noncomputable def pair12Alpha (S : CyclicStaircase) (i : Fin (pair12Count S.D)) : ℕ :=
  (orderedPair12Boundary S i).1.x - (i.1 + 1)

noncomputable def pair12Gamma (S : CyclicStaircase) (i : Fin (pair12Count S.D)) : ℕ :=
  (orderedPair12Boundary S i).1.y - (pair12Count S.D - i.1)

noncomputable def pair13Alpha (S : CyclicStaircase) (i : Fin (pair13Count S.D)) : ℕ :=
  (orderedPair13Boundary S i).1.x - (i.1 + 1)

noncomputable def pair13Gamma (S : CyclicStaircase) (i : Fin (pair13Count S.D)) : ℕ :=
  (orderedPair13Boundary S i).1.z - (pair13Count S.D - i.1)

noncomputable def pair23Alpha (S : CyclicStaircase) (i : Fin (pair23Count S.D)) : ℕ :=
  (orderedPair23Boundary S i).1.y - (i.1 + 1)

noncomputable def pair23Gamma (S : CyclicStaircase) (i : Fin (pair23Count S.D)) : ℕ :=
  (orderedPair23Boundary S i).1.z - (pair23Count S.D - i.1)

private theorem alpha_nondec_of_strictMono {n : ℕ} (f : Fin n → ℕ)
    (hf : StrictMono f) (hbase : ∀ i, i.1 + 1 ≤ f i) :
    Monotone (fun i => f i - (i.1 + 1)) := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
      apply Fin.monotone_iff_le_succ.mpr
      intro i
      have hlt : f i.castSucc < f i.succ := hf (by simp)
      have hb0 := hbase i.castSucc
      have hb1 := hbase i.succ
      change f i.castSucc - (i.1 + 1) ≤ f i.succ - (i.1 + 2)
      omega

private theorem gamma_noninc_of_strictAnti {n : ℕ} (f : Fin n → ℕ)
    (hf : StrictAnti f) (hbase : ∀ i, n - i.1 ≤ f i) :
    Antitone (fun i => f i - (n - i.1)) := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
      apply Fin.antitone_iff_succ_le.mpr
      intro i
      have hlt : f i.succ < f i.castSucc := hf (by simp)
      have hb0 := hbase i.castSucc
      have hb1 := hbase i.succ
      change f i.succ - (n + 1 - (i.1 + 1)) ≤
        f i.castSucc - (n + 1 - i.1)
      omega

theorem pair12Alpha_nondec (S : CyclicStaircase) : Monotone (pair12Alpha S) :=
  alpha_nondec_of_strictMono _ (orderedPair12Boundary_x_strictMono S)
    (orderedPair12Boundary_x_baseline S)

theorem pair12Gamma_noninc (S : CyclicStaircase) : Antitone (pair12Gamma S) :=
  gamma_noninc_of_strictAnti _ (orderedPair12Boundary_y_strictAnti S)
    (orderedPair12Boundary_y_baseline S)

theorem pair13Alpha_nondec (S : CyclicStaircase) : Monotone (pair13Alpha S) :=
  alpha_nondec_of_strictMono _ (orderedPair13Boundary_x_strictMono S)
    (orderedPair13Boundary_x_baseline S)

theorem pair13Gamma_noninc (S : CyclicStaircase) : Antitone (pair13Gamma S) :=
  gamma_noninc_of_strictAnti _ (orderedPair13Boundary_z_strictAnti S)
    (orderedPair13Boundary_z_baseline S)

theorem pair23Alpha_nondec (S : CyclicStaircase) : Monotone (pair23Alpha S) :=
  alpha_nondec_of_strictMono _ (orderedPair23Boundary_y_strictMono S)
    (orderedPair23Boundary_y_baseline S)

theorem pair23Gamma_noninc (S : CyclicStaircase) : Antitone (pair23Gamma S) :=
  gamma_noninc_of_strictAnti _ (orderedPair23Boundary_z_strictAnti S)
    (orderedPair23Boundary_z_baseline S)

end NSP3
