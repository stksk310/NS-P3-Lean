import NSP3.M5Baseline

namespace NSP3

theorem CyclicStaircase.zero_mem (S : CyclicStaircase) : Point3.zero ∈ S.D := by
  obtain ⟨p, hp⟩ := S.nonempty_D
  exact S.down_closed.mem_of_le
    (show Point3.zero ≤ p from ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩) hp

inductive SupportKind where
  | pure1 | pure2 | pure3 | pair12 | pair13 | pair23 | full
  deriving DecidableEq

def HasSupportKind : SupportKind → Point3 → Prop
  | .pure1, b => Pure1 b
  | .pure2, b => Pure2 b
  | .pure3, b => Pure3 b
  | .pair12, b => Pair12 b
  | .pair13, b => Pair13 b
  | .pair23, b => Pair23 b
  | .full, b => FullSupport b

theorem minimalComplement_support_cases (S : CyclicStaircase) {b : Point3}
    (hb : MinimalComplement S.D b) :
    Pure1 b ∨ Pure2 b ∨ Pure3 b ∨ Pair12 b ∨ Pair13 b ∨ Pair23 b ∨ FullSupport b := by
  by_cases hx : b.x = 0
  · by_cases hy : b.y = 0
    · by_cases hz : b.z = 0
      · have hzero : b = Point3.zero := by ext <;> simp [Point3.zero, hx, hy, hz]
        exact False.elim (hb.not_mem (hzero ▸ S.zero_mem))
      · exact Or.inr (Or.inr (Or.inl ⟨hx, hy, Nat.pos_of_ne_zero hz⟩))
    · by_cases hz : b.z = 0
      · exact Or.inr (Or.inl ⟨hx, Nat.pos_of_ne_zero hy, hz⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨hx, Nat.pos_of_ne_zero hy, Nat.pos_of_ne_zero hz⟩)))))
  · by_cases hy : b.y = 0
    · by_cases hz : b.z = 0
      · exact Or.inl ⟨Nat.pos_of_ne_zero hx, hy, hz⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl ⟨Nat.pos_of_ne_zero hx, hy, Nat.pos_of_ne_zero hz⟩))))
    · by_cases hz : b.z = 0
      · exact Or.inr (Or.inr (Or.inr
          (Or.inl ⟨Nat.pos_of_ne_zero hx, Nat.pos_of_ne_zero hy, hz⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨Nat.pos_of_ne_zero hx, Nat.pos_of_ne_zero hy, Nat.pos_of_ne_zero hz⟩)))))

private theorem hasSupportKind_unique {b : Point3} {k l : SupportKind}
    (hk : HasSupportKind k b) (hl : HasSupportKind l b) : k = l := by
  cases k <;> cases l <;>
    simp_all [HasSupportKind, Pure1, Pure2, Pure3, Pair12, Pair13, Pair23,
      FullSupport]

theorem minimalComplement_supportKind_unique (S : CyclicStaircase) {b : Point3}
    (hb : MinimalComplement S.D b) : ∃! k : SupportKind, HasSupportKind k b := by
  rcases minimalComplement_support_cases S hb with h | h | h | h | h | h | h
  · exact ⟨.pure1, h, fun _ hl => hasSupportKind_unique hl h⟩
  · exact ⟨.pure2, h, fun _ hl => hasSupportKind_unique hl h⟩
  · exact ⟨.pure3, h, fun _ hl => hasSupportKind_unique hl h⟩
  · exact ⟨.pair12, h, fun _ hl => hasSupportKind_unique hl h⟩
  · exact ⟨.pair13, h, fun _ hl => hasSupportKind_unique hl h⟩
  · exact ⟨.pair23, h, fun _ hl => hasSupportKind_unique hl h⟩
  · exact ⟨.full, h, fun _ hl => hasSupportKind_unique hl h⟩

def NoFullSupportBoundary (S : CyclicStaircase) : Prop :=
  ¬ ∃ g, MinimalComplement S.D g ∧ FullSupport g

theorem NoFullSupportBoundary.not_full {S : CyclicStaircase}
    (hnf : NoFullSupportBoundary S) {g : Point3}
    (hg : MinimalComplement S.D g) : ¬ FullSupport g := by
  intro hfull
  exact hnf ⟨g, hg, hfull⟩

theorem pair12_pair13_returns_ne (S : CyclicStaircase) {b c : Point3}
    (hb : MinimalComplement S.D b) (h12 : Pair12 b)
    (hc : MinimalComplement S.D c) (h13 : Pair13 c) : S.rho b ≠ S.rho c := by
  have hne : b ≠ c := by
    intro h
    subst c
    exact h13.2.2.ne' h12.2.2
  exact return_ne_of_support_inter S hb hc hne (Or.inl ⟨h12.1, h13.1⟩)

theorem pair12_pair23_returns_ne (S : CyclicStaircase) {b c : Point3}
    (hb : MinimalComplement S.D b) (h12 : Pair12 b)
    (hc : MinimalComplement S.D c) (h23 : Pair23 c) : S.rho b ≠ S.rho c := by
  have hne : b ≠ c := by
    intro h
    subst c
    exact (Nat.ne_of_gt h12.1) h23.1
  exact return_ne_of_support_inter S hb hc hne (Or.inr (Or.inl ⟨h12.2.1, h23.2.1⟩))

theorem pair13_pair23_returns_ne (S : CyclicStaircase) {b c : Point3}
    (hb : MinimalComplement S.D b) (h13 : Pair13 b)
    (hc : MinimalComplement S.D c) (h23 : Pair23 c) : S.rho b ≠ S.rho c := by
  have hne : b ≠ c := by
    intro h
    subst c
    exact (Nat.ne_of_gt h13.1) h23.1
  exact return_ne_of_support_inter S hb hc hne (Or.inr (Or.inr ⟨h13.2.2, h23.2.2⟩))

def PairBoundarySum (S : CyclicStaircase) :=
  Pair12Boundary S ⊕ (Pair13Boundary S ⊕ Pair23Boundary S)

noncomputable instance (S : CyclicStaircase) : Fintype (PairBoundarySum S) := by
  unfold PairBoundarySum
  infer_instance

def pairBoundaryPoint (S : CyclicStaircase) : PairBoundarySum S → Point3
  | .inl b => b.1
  | .inr (.inl b) => b.1
  | .inr (.inr b) => b.1

def pairBoundaryReturn (S : CyclicStaircase) (b : PairBoundarySum S) : Point3 :=
  S.rho (pairBoundaryPoint S b)

private theorem pairBoundarySum_eq_of_return_eq (S : CyclicStaircase)
    {b c : PairBoundarySum S} (hret : pairBoundaryReturn S b = pairBoundaryReturn S c) :
    b = c := by
  cases b with
  | inl b =>
      cases c with
      | inl c =>
          congr 1
          apply Subtype.ext
          by_contra hne
          exact (return_ne_of_support_inter S b.2.1 c.2.1 hne
            (Or.inl ⟨b.2.2.1, c.2.2.1⟩)) hret
      | inr c =>
          cases c with
          | inl c => exact
              ((pair12_pair13_returns_ne S b.2.1 b.2.2 c.2.1 c.2.2) hret).elim
          | inr c => exact
              ((pair12_pair23_returns_ne S b.2.1 b.2.2 c.2.1 c.2.2) hret).elim
  | inr b =>
      cases b with
      | inl b =>
          cases c with
          | inl c => exact
              ((pair12_pair13_returns_ne S c.2.1 c.2.2 b.2.1 b.2.2) hret.symm).elim
          | inr c =>
              cases c with
              | inl c =>
                  congr 2
                  apply Subtype.ext
                  by_contra hne
                  exact (return_ne_of_support_inter S b.2.1 c.2.1 hne
                    (Or.inl ⟨b.2.2.1, c.2.2.1⟩)) hret
              | inr c => exact
                  ((pair13_pair23_returns_ne S b.2.1 b.2.2 c.2.1 c.2.2) hret).elim
      | inr b =>
          cases c with
          | inl c => exact
              ((pair12_pair23_returns_ne S c.2.1 c.2.2 b.2.1 b.2.2) hret.symm).elim
          | inr c =>
              cases c with
              | inl c => exact
                  ((pair13_pair23_returns_ne S c.2.1 c.2.2 b.2.1 b.2.2) hret.symm).elim
              | inr c =>
                  congr 2
                  apply Subtype.ext
                  by_contra hne
                  exact (return_ne_of_support_inter S b.2.1 c.2.1 hne
                    (Or.inr (Or.inl ⟨b.2.2.2.1, c.2.2.2.1⟩))) hret

noncomputable def zeroReturningPairBoundaries (S : CyclicStaircase) :
    Finset (PairBoundarySum S) := by
  classical
  exact Finset.univ.filter fun b => pairBoundaryReturn S b = Point3.zero

theorem zeroReturningPairBoundaries_card_le_one (S : CyclicStaircase)
    (_hnf : NoFullSupportBoundary S) : (zeroReturningPairBoundaries S).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro b hb c hc
  have hbzero : pairBoundaryReturn S b = Point3.zero := by
    simpa [zeroReturningPairBoundaries] using hb
  have hczero : pairBoundaryReturn S c = Point3.zero := by
    simpa [zeroReturningPairBoundaries] using hc
  exact pairBoundarySum_eq_of_return_eq S (hbzero.trans hczero.symm)

end NSP3
