import NSP3.PairFerrers

namespace NSP3

/-- Strictly ordered pairs `i < j < q`, used to index the positive Ferrers triangle. -/
def pairTriangleIndices (q : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range q).product (Finset.range q)).filter fun p => p.1 < p.2

@[simp] theorem card_pairTriangleIndices (q : ℕ) :
    (pairTriangleIndices q).card = Nat.choose q 2 := by
  simpa [pairTriangleIndices] using
    (Finset.card_product_filter_lt (s := Finset.range q))

noncomputable def pair12PlaneSection (D : Finset Point3) : Finset Point3 := by
  classical
  exact D.filter fun p => p.z = 0

def Pair12PlaneSource (a₁ a₂ q : ℕ) :=
  Fin a₁ ⊕ (Fin (a₂ - 1) ⊕ {p : ℕ × ℕ // p ∈ pairTriangleIndices q})

instance (a₁ a₂ q : ℕ) : Fintype (Pair12PlaneSource a₁ a₂ q) := by
  unfold Pair12PlaneSource
  infer_instance

def pair12SourcePoint {a₁ a₂ q : ℕ} : Pair12PlaneSource a₁ a₂ q → Point3
  | Sum.inl i => ⟨i, 0, 0⟩
  | Sum.inr (Sum.inl j) => ⟨0, j + 1, 0⟩
  | Sum.inr (Sum.inr p) => ⟨p.1.1 + 1, p.1.2 - p.1.1, 0⟩

theorem pair12SourcePoint_injective {a₁ a₂ q : ℕ} :
    Function.Injective (@pair12SourcePoint a₁ a₂ q) := by
  intro s t h
  rcases s with i | s
  · rcases t with j | t
    · congr
      apply Fin.ext
      exact congrArg Point3.x h
    · rcases t with j | p
      · have hy := congrArg Point3.y h
        simp [pair12SourcePoint] at hy
      · have hp := Finset.mem_filter.mp p.2
        have hpord : p.1.1 < p.1.2 := hp.2
        have hy := congrArg Point3.y h
        simp [pair12SourcePoint] at hy
        omega
  · rcases s with i | p
    · rcases t with j | t
      · have hy := congrArg Point3.y h
        simp [pair12SourcePoint] at hy
      · rcases t with j | r
        · congr
          apply Fin.ext
          have hy := congrArg Point3.y h
          simpa [pair12SourcePoint] using hy
        · have hr := Finset.mem_filter.mp r.2
          have hrord : r.1.1 < r.1.2 := hr.2
          have hx := congrArg Point3.x h
          simp [pair12SourcePoint] at hx
    · rcases t with j | t
      · have hp := Finset.mem_filter.mp p.2
        have hpord : p.1.1 < p.1.2 := hp.2
        have hy := congrArg Point3.y h
        simp [pair12SourcePoint] at hy
        omega
      · rcases t with j | r
        · have hp := Finset.mem_filter.mp p.2
          have hpord : p.1.1 < p.1.2 := hp.2
          have hx := congrArg Point3.x h
          simp [pair12SourcePoint] at hx
        · congr
          apply Subtype.ext
          apply Prod.ext
          · have hx := congrArg Point3.x h
            simpa [pair12SourcePoint] using hx
          · have hp := Finset.mem_filter.mp p.2
            have hr := Finset.mem_filter.mp r.2
            have hpord : p.1.1 < p.1.2 := hp.2
            have hrord : r.1.1 < r.1.2 := hr.2
            have hx := congrArg Point3.x h
            have hy := congrArg Point3.y h
            simp [pair12SourcePoint] at hx hy
            omega

theorem pair12Plane_card_lower {D : Finset Point3} (hD : IsDownset D)
    {a₁ a₂ : ℕ}
    (h₁ : MinimalComplement D ⟨a₁, 0, 0⟩) (hp₁ : Pure1 ⟨a₁, 0, 0⟩)
    (h₂ : MinimalComplement D ⟨0, a₂, 0⟩) (hp₂ : Pure2 ⟨0, a₂, 0⟩) :
    a₁ + a₂ - 1 + Nat.choose (pair12Count D) 2 ≤ (pair12PlaneSection D).card := by
  classical
  let q := pair12Count D
  let source := Pair12PlaneSource a₁ a₂ q
  let target := {p : Point3 // p ∈ pair12PlaneSection D}
  have hsource_mem (s : source) : pair12SourcePoint s ∈ pair12PlaneSection D := by
    rcases s with i | s
    · apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      have hpred := h₁.pred1_mem hp₁.1
      apply hD.mem_of_le (b := Point3.pred1 ⟨a₁, 0, 0⟩) ?_ hpred
      change Point3.mk i.1 0 0 ≤ Point3.pred1 ⟨a₁, 0, 0⟩
      exact ⟨by simp [Point3.pred1]; omega, by simp [Point3.pred1],
        by simp [Point3.pred1]⟩
    · rcases s with j | p
      · apply Finset.mem_filter.mpr
        refine ⟨?_, rfl⟩
        have hpred := h₂.pred2_mem hp₂.2.1
        apply hD.mem_of_le (b := Point3.pred2 ⟨0, a₂, 0⟩) ?_ hpred
        change Point3.mk 0 (j.1 + 1) 0 ≤ Point3.pred2 ⟨0, a₂, 0⟩
        exact ⟨by simp [Point3.pred2], by simp [Point3.pred2],
          by simp [Point3.pred2]⟩
      · apply Finset.mem_filter.mpr
        refine ⟨?_, rfl⟩
        have hp := Finset.mem_filter.mp p.2
        have hprange := Finset.mem_product.mp hp.1
        have hi : p.1.1 < q := Finset.mem_range.mp hprange.1
        have hj : p.1.2 < q := Finset.mem_range.mp hprange.2
        have hij : p.1.1 < p.1.2 := hp.2
        apply pair12Triangle_subset hD
        · omega
        · omega
        · change p.1.1 + 1 + (p.1.2 - p.1.1) ≤ q
          omega
  let f : source → target := fun s => ⟨pair12SourcePoint s, hsource_mem s⟩
  have hf : Function.Injective f := by
    intro s t h
    apply pair12SourcePoint_injective
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  have hsourcecard : Fintype.card source =
      a₁ + (a₂ - 1) + Nat.choose q 2 := by
    simp [source, Pair12PlaneSource, card_pairTriangleIndices, Nat.add_assoc]
  have htargetcard : Fintype.card target = (pair12PlaneSection D).card := by
    simp [target]
  rw [hsourcecard, htargetcard] at hcard
  have ha₂pos : 0 < a₂ := hp₂.2.1
  simpa [q] using (show a₁ + a₂ - 1 + Nat.choose q 2 ≤
    (pair12PlaneSection D).card by omega)

noncomputable def pair13PlaneSection (D : Finset Point3) : Finset Point3 := by
  classical
  exact D.filter fun p => p.y = 0

noncomputable def pair23PlaneSection (D : Finset Point3) : Finset Point3 := by
  classical
  exact D.filter fun p => p.x = 0

private def swapYZ (p : Point3) : Point3 := ⟨p.x, p.z, p.y⟩
private def rotateTo23 (p : Point3) : Point3 := ⟨p.z, p.x, p.y⟩

private theorem swapYZ_injective : Function.Injective swapYZ := by
  intro a b h
  apply Point3.ext
  · simpa [swapYZ] using congrArg Point3.x h
  · simpa [swapYZ] using congrArg Point3.z h
  · simpa [swapYZ] using congrArg Point3.y h

private theorem rotateTo23_injective : Function.Injective rotateTo23 := by
  intro a b h
  apply Point3.ext
  · simpa [rotateTo23] using congrArg Point3.y h
  · simpa [rotateTo23] using congrArg Point3.z h
  · simpa [rotateTo23] using congrArg Point3.x h

private def pair13SourcePoint {a₁ a₃ q : ℕ} (s : Pair12PlaneSource a₁ a₃ q) : Point3 :=
  swapYZ (pair12SourcePoint s)

private def pair23SourcePoint {a₂ a₃ q : ℕ} (s : Pair12PlaneSource a₂ a₃ q) : Point3 :=
  rotateTo23 (pair12SourcePoint s)

private theorem pair13SourcePoint_injective {a₁ a₃ q : ℕ} :
    Function.Injective (@pair13SourcePoint a₁ a₃ q) :=
  swapYZ_injective.comp pair12SourcePoint_injective

private theorem pair23SourcePoint_injective {a₂ a₃ q : ℕ} :
    Function.Injective (@pair23SourcePoint a₂ a₃ q) :=
  rotateTo23_injective.comp pair12SourcePoint_injective

theorem pair13Plane_card_lower {D : Finset Point3} (hD : IsDownset D)
    {a₁ a₃ : ℕ}
    (h₁ : MinimalComplement D ⟨a₁, 0, 0⟩) (hp₁ : Pure1 ⟨a₁, 0, 0⟩)
    (h₃ : MinimalComplement D ⟨0, 0, a₃⟩) (hp₃ : Pure3 ⟨0, 0, a₃⟩) :
    a₁ + a₃ - 1 + Nat.choose (pair13Count D) 2 ≤ (pair13PlaneSection D).card := by
  classical
  let q := pair13Count D
  let source := Pair12PlaneSource a₁ a₃ q
  let target := {p : Point3 // p ∈ pair13PlaneSection D}
  have hsource_mem (s : source) : pair13SourcePoint s ∈ pair13PlaneSection D := by
    rcases s with i | s
    · apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      have hpred := h₁.pred1_mem hp₁.1
      apply hD.mem_of_le (b := Point3.pred1 ⟨a₁, 0, 0⟩) ?_ hpred
      change Point3.mk i.1 0 0 ≤ Point3.pred1 ⟨a₁, 0, 0⟩
      exact ⟨by simp [Point3.pred1]; omega, by simp [Point3.pred1],
        by simp [Point3.pred1]⟩
    · rcases s with j | p
      · apply Finset.mem_filter.mpr
        refine ⟨?_, rfl⟩
        have hpred := h₃.pred3_mem hp₃.2.2
        apply hD.mem_of_le (b := Point3.pred3 ⟨0, 0, a₃⟩) ?_ hpred
        change Point3.mk 0 0 (j.1 + 1) ≤ Point3.pred3 ⟨0, 0, a₃⟩
        exact ⟨by simp [Point3.pred3], by simp [Point3.pred3],
          by simp [Point3.pred3]⟩
      · apply Finset.mem_filter.mpr
        refine ⟨?_, rfl⟩
        have hp := Finset.mem_filter.mp p.2
        have hprange := Finset.mem_product.mp hp.1
        have hi : p.1.1 < q := Finset.mem_range.mp hprange.1
        have hj : p.1.2 < q := Finset.mem_range.mp hprange.2
        have hij : p.1.1 < p.1.2 := hp.2
        change Point3.mk (p.1.1 + 1) 0 (p.1.2 - p.1.1) ∈ D
        apply pair13Triangle_subset hD
        · omega
        · omega
        · change p.1.1 + 1 + (p.1.2 - p.1.1) ≤ q
          omega
  let f : source → target := fun s => ⟨pair13SourcePoint s, hsource_mem s⟩
  have hf : Function.Injective f := by
    intro s t h
    apply pair13SourcePoint_injective
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  have hsourcecard : Fintype.card source =
      a₁ + (a₃ - 1) + Nat.choose q 2 := by
    simp [source, Pair12PlaneSource, card_pairTriangleIndices, Nat.add_assoc]
  have htargetcard : Fintype.card target = (pair13PlaneSection D).card := by
    simp [target]
  rw [hsourcecard, htargetcard] at hcard
  have ha₃pos : 0 < a₃ := hp₃.2.2
  simpa [q] using (show a₁ + a₃ - 1 + Nat.choose q 2 ≤
    (pair13PlaneSection D).card by omega)

theorem pair23Plane_card_lower {D : Finset Point3} (hD : IsDownset D)
    {a₂ a₃ : ℕ}
    (h₂ : MinimalComplement D ⟨0, a₂, 0⟩) (hp₂ : Pure2 ⟨0, a₂, 0⟩)
    (h₃ : MinimalComplement D ⟨0, 0, a₃⟩) (hp₃ : Pure3 ⟨0, 0, a₃⟩) :
    a₂ + a₃ - 1 + Nat.choose (pair23Count D) 2 ≤ (pair23PlaneSection D).card := by
  classical
  let q := pair23Count D
  let source := Pair12PlaneSource a₂ a₃ q
  let target := {p : Point3 // p ∈ pair23PlaneSection D}
  have hsource_mem (s : source) : pair23SourcePoint s ∈ pair23PlaneSection D := by
    rcases s with i | s
    · apply Finset.mem_filter.mpr
      refine ⟨?_, rfl⟩
      have hpred := h₂.pred2_mem hp₂.2.1
      apply hD.mem_of_le (b := Point3.pred2 ⟨0, a₂, 0⟩) ?_ hpred
      change Point3.mk 0 i.1 0 ≤ Point3.pred2 ⟨0, a₂, 0⟩
      exact ⟨by simp [Point3.pred2], by simp [Point3.pred2]; omega,
        by simp [Point3.pred2]⟩
    · rcases s with j | p
      · apply Finset.mem_filter.mpr
        refine ⟨?_, rfl⟩
        have hpred := h₃.pred3_mem hp₃.2.2
        apply hD.mem_of_le (b := Point3.pred3 ⟨0, 0, a₃⟩) ?_ hpred
        change Point3.mk 0 0 (j.1 + 1) ≤ Point3.pred3 ⟨0, 0, a₃⟩
        exact ⟨by simp [Point3.pred3], by simp [Point3.pred3],
          by simp [Point3.pred3]⟩
      · apply Finset.mem_filter.mpr
        refine ⟨?_, rfl⟩
        have hp := Finset.mem_filter.mp p.2
        have hprange := Finset.mem_product.mp hp.1
        have hi : p.1.1 < q := Finset.mem_range.mp hprange.1
        have hj : p.1.2 < q := Finset.mem_range.mp hprange.2
        have hij : p.1.1 < p.1.2 := hp.2
        change Point3.mk 0 (p.1.1 + 1) (p.1.2 - p.1.1) ∈ D
        apply pair23Triangle_subset hD
        · omega
        · omega
        · change p.1.1 + 1 + (p.1.2 - p.1.1) ≤ q
          omega
  let f : source → target := fun s => ⟨pair23SourcePoint s, hsource_mem s⟩
  have hf : Function.Injective f := by
    intro s t h
    apply pair23SourcePoint_injective
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  have hsourcecard : Fintype.card source =
      a₂ + (a₃ - 1) + Nat.choose q 2 := by
    simp [source, Pair12PlaneSource, card_pairTriangleIndices, Nat.add_assoc]
  have htargetcard : Fintype.card target = (pair23PlaneSection D).card := by
    simp [target]
  rw [hsourcecard, htargetcard] at hcard
  have ha₃pos : 0 < a₃ := hp₃.2.2
  simpa [q] using (show a₂ + a₃ - 1 + Nat.choose q 2 ≤
    (pair23PlaneSection D).card by omega)

end NSP3
