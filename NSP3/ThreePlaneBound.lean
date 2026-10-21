import NSP3.PureIntercepts
import NSP3.FerrersCardinality

namespace NSP3


def TriangleIndex (q : ℕ) := {p : ℕ × ℕ // p ∈ pairTriangleIndices q}

def ThreePlaneSource (S : CyclicStaircase) :=
  Unit ⊕ (Fin (pure1Intercept S - 1) ⊕
    (Fin (pure2Intercept S - 1) ⊕
      (Fin (pure3Intercept S - 1) ⊕
        (TriangleIndex (pair12Count S.D) ⊕
          (TriangleIndex (pair13Count S.D) ⊕
            TriangleIndex (pair23Count S.D))))))

noncomputable instance (S : CyclicStaircase) : Fintype (ThreePlaneSource S) := by
  unfold ThreePlaneSource TriangleIndex
  infer_instance

def threePlaneSourcePoint (S : CyclicStaircase) : ThreePlaneSource S → Point3
  | Sum.inl _ => ⟨0, 0, 0⟩
  | Sum.inr (Sum.inl i) => ⟨i.1 + 1, 0, 0⟩
  | Sum.inr (Sum.inr (Sum.inl j)) => ⟨0, j.1 + 1, 0⟩
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl k))) => ⟨0, 0, k.1 + 1⟩
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p)))) =>
      ⟨p.1.1 + 1, p.1.2 - p.1.1, 0⟩
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))) =>
      ⟨p.1.1 + 1, 0, p.1.2 - p.1.1⟩
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))) =>
      ⟨0, p.1.1 + 1, p.1.2 - p.1.1⟩

private theorem triangleIndex_order {q : ℕ} (p : TriangleIndex q) :
    p.1.1 < p.1.2 :=
  (Finset.mem_filter.mp p.2).2

@[simp] private theorem triangleIndex_sub_ne_zero {q : ℕ} (p : TriangleIndex q) :
    p.1.2 - p.1.1 ≠ 0 := by
  have := triangleIndex_order p
  omega

private theorem triangleIndex_eq_of_coords {q : ℕ} {p r : TriangleIndex q}
    (hfirst : p.1.1 = r.1.1)
    (hdiff : p.1.2 - p.1.1 = r.1.2 - r.1.1) : p = r := by
  have hporder := triangleIndex_order p
  have hrorder := triangleIndex_order r
  apply Subtype.ext
  apply Prod.ext
  · exact hfirst
  · omega

private def threePlanePointTag (p : Point3) : ℕ :=
  if p.x = 0 then
    if p.y = 0 then
      if p.z = 0 then 0 else 3
    else
      if p.z = 0 then 2 else 6
  else
    if p.y = 0 then
      if p.z = 0 then 1 else 5
    else 4

private def threePlaneSourceTag (S : CyclicStaircase) : ThreePlaneSource S → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (Sum.inl _)) => 2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 3
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => 4
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _))))) => 5
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr _))))) => 6

private theorem threePlanePointTag_source (S : CyclicStaircase)
    (s : ThreePlaneSource S) :
    threePlanePointTag (threePlaneSourcePoint S s) = threePlaneSourceTag S s := by
  rcases s with _ | i | j | k | p | p | p <;>
    simp [threePlanePointTag, threePlaneSourceTag, threePlaneSourcePoint]

theorem threePlaneSourcePoint_mem (S : CyclicStaircase)
    (s : ThreePlaneSource S) : threePlaneSourcePoint S s ∈ S.D := by
  rcases s with _ | i | j | k | p | p | p
  · simpa [threePlaneSourcePoint, Point3.zero] using
      (pure1_axis_mem_iff S 0).mpr (pure1Intercept_pure S).1
  · apply (pure1_axis_mem_iff S (i.1 + 1)).mpr
    omega
  · apply (pure2_axis_mem_iff S (j.1 + 1)).mpr
    omega
  · apply (pure3_axis_mem_iff S (k.1 + 1)).mpr
    omega
  · have hp := Finset.mem_filter.mp p.2
    have hrange := Finset.mem_product.mp hp.1
    have hi : p.1.1 < pair12Count S.D := Finset.mem_range.mp hrange.1
    have hj : p.1.2 < pair12Count S.D := Finset.mem_range.mp hrange.2
    have hij : p.1.1 < p.1.2 := hp.2
    apply pair12Triangle_subset S.down_closed
    · omega
    · omega
    · omega
  · have hp := Finset.mem_filter.mp p.2
    have hrange := Finset.mem_product.mp hp.1
    have hi : p.1.1 < pair13Count S.D := Finset.mem_range.mp hrange.1
    have hj : p.1.2 < pair13Count S.D := Finset.mem_range.mp hrange.2
    have hij : p.1.1 < p.1.2 := hp.2
    apply pair13Triangle_subset S.down_closed
    · omega
    · omega
    · omega
  · have hp := Finset.mem_filter.mp p.2
    have hrange := Finset.mem_product.mp hp.1
    have hi : p.1.1 < pair23Count S.D := Finset.mem_range.mp hrange.1
    have hj : p.1.2 < pair23Count S.D := Finset.mem_range.mp hrange.2
    have hij : p.1.1 < p.1.2 := hp.2
    apply pair23Triangle_subset S.down_closed
    · omega
    · omega
    · omega

theorem threePlaneSourcePoint_injective (S : CyclicStaircase) :
    Function.Injective (threePlaneSourcePoint S) := by
  intro s t h
  have htag : threePlaneSourceTag S s = threePlaneSourceTag S t := by
    rw [← threePlanePointTag_source S s, ← threePlanePointTag_source S t, h]
  rcases s with u | i | j | k | p12 | p13 | p23 <;>
    rcases t with v | i' | j' | k' | r12 | r13 | r23 <;>
    simp [threePlaneSourceTag] at htag
  · cases u
    cases v
    rfl
  · have hv := congrArg Point3.x h
    have hij : i = i' := Fin.ext (by simpa [threePlaneSourcePoint] using hv)
    cases hij
    rfl
  · have hv := congrArg Point3.y h
    have hij : j = j' := Fin.ext (by simpa [threePlaneSourcePoint] using hv)
    cases hij
    rfl
  · have hv := congrArg Point3.z h
    have hij : k = k' := Fin.ext (by simpa [threePlaneSourcePoint] using hv)
    cases hij
    rfl
  · have hx := congrArg Point3.x h
    have hy := congrArg Point3.y h
    have hpr : p12 = r12 := triangleIndex_eq_of_coords
      (by simpa [threePlaneSourcePoint] using hx)
      (by simpa [threePlaneSourcePoint] using hy)
    cases hpr
    rfl
  · have hx := congrArg Point3.x h
    have hz := congrArg Point3.z h
    have hpr : p13 = r13 := triangleIndex_eq_of_coords
      (by simpa [threePlaneSourcePoint] using hx)
      (by simpa [threePlaneSourcePoint] using hz)
    cases hpr
    rfl
  · have hy := congrArg Point3.y h
    have hz := congrArg Point3.z h
    have hpr : p23 = r23 := triangleIndex_eq_of_coords
      (by simpa [threePlaneSourcePoint] using hy)
      (by simpa [threePlaneSourcePoint] using hz)
    cases hpr
    rfl

@[simp] theorem card_threePlaneSource (S : CyclicStaircase) :
    Fintype.card (ThreePlaneSource S) =
      1 + (pure1Intercept S - 1) + (pure2Intercept S - 1) +
        (pure3Intercept S - 1) + Nat.choose (pair12Count S.D) 2 +
        Nat.choose (pair13Count S.D) 2 + Nat.choose (pair23Count S.D) 2 := by
  simp [ThreePlaneSource, TriangleIndex, card_pairTriangleIndices, Nat.add_assoc]

theorem threePlane_card_lower_D (S : CyclicStaircase) :
    pure1Intercept S + pure2Intercept S + pure3Intercept S - 2
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2 ≤ S.D.card := by
  classical
  let target := {p : Point3 // p ∈ S.D}
  let f : ThreePlaneSource S → target := fun s =>
    ⟨threePlaneSourcePoint S s, threePlaneSourcePoint_mem S s⟩
  have hf : Function.Injective f := by
    intro s t h
    apply threePlaneSourcePoint_injective S
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  have htarget : Fintype.card target = S.D.card := by simp [target]
  rw [card_threePlaneSource, htarget] at hcard
  have h1 := (pure1Intercept_pure S).1
  have h2 := (pure2Intercept_pure S).2.1
  have h3 := (pure3Intercept_pure S).2.2
  omega

theorem threePlane_card_lower (S : CyclicStaircase) :
    pure1Intercept S + pure2Intercept S + pure3Intercept S - 2
        + Nat.choose (pair12Count S.D) 2
        + Nat.choose (pair13Count S.D) 2
        + Nat.choose (pair23Count S.D) 2 ≤ S.m := by
  simpa [S.card_D] using threePlane_card_lower_D S

end NSP3
