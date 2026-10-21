import NSP3.ReturnSpacing

namespace NSP3


theorem m5_fullCore_lower_equal (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (heq : pair12Count S.D = pair13Count S.D) :
    3 * pair12Count S.D + 1
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + (fullCoreFinset S).card ≤ S.m := by
  have hcard := threePlane_fullCore_card_lower S hnf
  have hm4 := m4_intercepts_equal S hord heq
  have hD := S.card_D
  have h1 := (pure1Intercept_pure S).1
  have h2 := (pure2Intercept_pure S).2.1
  have h3 := (pure3Intercept_pure S).2.2
  omega

theorem m5_fullCore_lower_strict (S : CyclicStaircase)
    (hnf : NoFullSupportBoundary S) (hord : PairCountsOrdered S)
    (hlt : pair13Count S.D < pair12Count S.D) :
    3 * pair12Count S.D
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2
        + (fullCoreFinset S).card ≤ S.m := by
  have hcard := threePlane_fullCore_card_lower S hnf
  have hm4 := m4_intercepts_strict S hord hlt
  have hD := S.card_D
  have h1 := (pure1Intercept_pure S).1
  have h2 := (pure2Intercept_pure S).2.1
  have h3 := (pure3Intercept_pure S).2.2
  omega

private theorem card_le_fullCore (S : CyclicStaircase) {A : Type}
    [Fintype A] (f : A → Point3) (hf : Function.Injective f)
    (hcore : ∀ a, FullCore S (f a)) :
    Fintype.card A ≤ (fullCoreFinset S).card := by
  classical
  let g : A → {p : Point3 // p ∈ fullCoreFinset S} :=
    fun a => ⟨f a, (mem_fullCoreFinset S (f a)).mpr (hcore a)⟩
  have hg : Function.Injective g := by
    intro a b h
    apply hf
    exact congrArg Subtype.val h
  simpa using Fintype.card_le_of_injective g hg

private def coreT2Point (i : Fin (s - 1)) : Point3 :=
  ⟨i.1 + 1, 1, 1⟩

private theorem coreT2Point_injective (s : ℕ) :
    Function.Injective (@coreT2Point s) := by
  intro i j h
  apply Fin.ext
  have hx := congrArg Point3.x h
  simp [coreT2Point] at hx
  omega

theorem fullCore_card_lower_t2 (S : CyclicStaircase)
    (hr : pair13Count S.D < pair12Count S.D)
    (ht : pair23Count S.D = 2) :
    pair13Count S.D - 1 ≤ (fullCoreFinset S).card := by
  let s := pair13Count S.D
  have hcard := card_le_fullCore S (@coreT2Point s) (coreT2Point_injective s) (by
    intro i
    unfold FullCore coreT2Point
    dsimp [s] at i ⊢
    have hi := i.2
    omega)
  simpa [s] using hcard

private abbrev CoreT3Source (s : ℕ) :=
  Fin (s - 1) ⊕ (Fin (s - 2) ⊕ Fin (s - 1))

private def coreT3Point {s : ℕ} : CoreT3Source s → Point3
  | .inl i => ⟨i.1 + 1, 1, 1⟩
  | .inr (.inl i) => ⟨i.1 + 1, 1, 2⟩
  | .inr (.inr i) => ⟨i.1 + 1, 2, 1⟩

private theorem coreT3Point_injective (s : ℕ) :
    Function.Injective (@coreT3Point s) := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · apply congrArg Sum.inl
    apply Fin.ext
    simpa [coreT3Point] using congrArg Point3.x h
  · rcases b with b | b <;> simp [coreT3Point] at h
  · rcases a with a | a <;> simp [coreT3Point] at h
  · rcases a with a | a <;> rcases b with b | b
    · apply congrArg (fun x => Sum.inr (Sum.inl x))
      apply Fin.ext
      simpa [coreT3Point] using congrArg Point3.x h
    · simp [coreT3Point] at h
    · simp [coreT3Point] at h
    · apply congrArg (fun x => Sum.inr (Sum.inr x))
      apply Fin.ext
      simpa [coreT3Point] using congrArg Point3.x h

theorem fullCore_card_lower_t3 (S : CyclicStaircase)
    (hord : PairCountsOrdered S)
    (hr : pair13Count S.D < pair12Count S.D)
    (ht : pair23Count S.D = 3) :
    3 * pair13Count S.D - 4 ≤ (fullCoreFinset S).card := by
  let s := pair13Count S.D
  have hs : 3 ≤ s := by
    have horder := hord.1
    dsimp [s]
    omega
  have hcard := card_le_fullCore S (@coreT3Point s) (coreT3Point_injective s) (by
    intro a
    rcases a with i | a
    · unfold FullCore coreT3Point
      dsimp [s] at i ⊢
      have hi := i.2
      omega
    · rcases a with i | i
      · unfold FullCore coreT3Point
        dsimp [s] at i ⊢
        have hi := i.2
        omega
      · unfold FullCore coreT3Point
        dsimp [s] at i ⊢
        have hi := i.2
        omega)
  have hsource : Fintype.card (CoreT3Source s) = 3 * s - 4 := by
    simp
    omega
  rw [hsource] at hcard
  simpa [s] using hcard

private abbrev Core44Source :=
  (Fin 3 × Fin 3) ⊕ ((Fin 2 × Fin 2) ⊕ (Fin 1 × Fin 1))

private def core44Point : Core44Source → Point3
  | .inl a => ⟨a.1.1 + 1, a.2.1 + 1, 1⟩
  | .inr (.inl a) => ⟨a.1.1 + 1, a.2.1 + 1, 2⟩
  | .inr (.inr a) => ⟨a.1.1 + 1, a.2.1 + 1, 3⟩

private theorem core44Point_injective : Function.Injective core44Point := by
  intro a b h
  rcases a with a | a <;> rcases b with b | b
  · apply congrArg Sum.inl
    apply Prod.ext <;> apply Fin.ext
    · simpa [core44Point] using congrArg Point3.x h
    · simpa [core44Point] using congrArg Point3.y h
  · rcases b with b | b <;> simp [core44Point] at h
  · rcases a with a | a <;> simp [core44Point] at h
  · rcases a with a | a <;> rcases b with b | b
    · apply congrArg (fun x => Sum.inr (Sum.inl x))
      apply Prod.ext <;> apply Fin.ext
      · simpa [core44Point] using congrArg Point3.x h
      · simpa [core44Point] using congrArg Point3.y h
    · simp [core44Point] at h
    · simp [core44Point] at h
    · apply congrArg (fun x => Sum.inr (Sum.inr x))
      apply Prod.ext <;> apply Fin.ext
      · simp
      · simp

theorem fullCore_card_lower_44_large (S : CyclicStaircase)
    (hr : 6 ≤ pair12Count S.D)
    (hs : pair13Count S.D = 4) (ht : pair23Count S.D = 4) :
    14 ≤ (fullCoreFinset S).card := by
  have hcard := card_le_fullCore S core44Point core44Point_injective (by
    intro a
    rcases a with a | a
    · change FullCore S ⟨a.1.1 + 1, a.2.1 + 1, 1⟩
      unfold FullCore
      simp only
      have h1 := a.1.2
      have h2 := a.2.2
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · rcases a with a | a
      · change FullCore S ⟨a.1.1 + 1, a.2.1 + 1, 2⟩
        unfold FullCore
        simp only
        have h1 := a.1.2
        have h2 := a.2.2
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      · change FullCore S ⟨a.1.1 + 1, a.2.1 + 1, 3⟩
        unfold FullCore
        simp only
        have h1 := a.1.2
        have h2 := a.2.2
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)
  have hsource : Fintype.card Core44Source = 14 := by decide
  rw [hsource] at hcard
  exact hcard

private abbrev Core544Source :=
  {a : Core44Source // (core44Point a).x + (core44Point a).y ≤ 5}

private theorem card_Core544Source : Fintype.card Core544Source = 13 := by
  decide

theorem fullCore_card_lower_544 (S : CyclicStaircase)
    (hr : pair12Count S.D = 5)
    (hs : pair13Count S.D = 4) (ht : pair23Count S.D = 4) :
    13 ≤ (fullCoreFinset S).card := by
  let f : Core544Source → Point3 := fun a => core44Point a.1
  have hf : Function.Injective f := core44Point_injective.comp Subtype.val_injective
  have hcard := card_le_fullCore S f hf (by
    rintro ⟨a, hxy⟩
    dsimp [f]
    rcases a with a | a
    · change a.1.1 + 1 + (a.2.1 + 1) ≤ 5 at hxy
      change FullCore S ⟨a.1.1 + 1, a.2.1 + 1, 1⟩
      unfold FullCore
      simp only
      have h1 := a.1.2
      have h2 := a.2.2
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
    · rcases a with a | a
      · change a.1.1 + 1 + (a.2.1 + 1) ≤ 5 at hxy
        change FullCore S ⟨a.1.1 + 1, a.2.1 + 1, 2⟩
        unfold FullCore
        simp only
        have h1 := a.1.2
        have h2 := a.2.2
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
      · change a.1.1 + 1 + (a.2.1 + 1) ≤ 5 at hxy
        change FullCore S ⟨a.1.1 + 1, a.2.1 + 1, 3⟩
        unfold FullCore
        simp only
        have h1 := a.1.2
        have h2 := a.2.2
        exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩)
  rw [card_Core544Source] at hcard
  exact hcard

end NSP3
