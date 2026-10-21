import NSP3.PureIntercepts
import NSP3.PairBoundaryCounts

namespace NSP3


theorem fullSupport_return_eq_zero (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    S.rho g = Point3.zero := by
  apply Point3.ext
  · simpa [Point3.zero] using complementFaceReturn₁ S hg hfull.1
  · simpa [Point3.zero] using complementFaceReturn₂ S hg hfull.2.1
  · simpa [Point3.zero] using complementFaceReturn₃ S hg hfull.2.2

theorem pair12_return_ne_zero_of_fullSupport (S : CyclicStaircase) {g b : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hb : MinimalComplement S.D b) (hp : Pair12 b) : S.rho b ≠ Point3.zero := by
  have hbg : b ≠ g := by
    intro h
    subst g
    have := hfull.2.2
    rw [hp.2.2] at this
    omega
  have hne := return_ne_of_support_inter S hb hg hbg (Or.inl ⟨hp.1, hfull.1⟩)
  intro hr
  apply hne
  calc
    S.rho b = Point3.zero := hr
    _ = S.rho g := (fullSupport_return_eq_zero S hg hfull).symm

theorem pair13_return_ne_zero_of_fullSupport (S : CyclicStaircase) {g b : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hb : MinimalComplement S.D b) (hp : Pair13 b) : S.rho b ≠ Point3.zero := by
  have hbg : b ≠ g := by
    intro h
    subst g
    have := hfull.2.1
    rw [hp.2.1] at this
    omega
  have hne := return_ne_of_support_inter S hb hg hbg (Or.inl ⟨hp.1, hfull.1⟩)
  intro hr
  apply hne
  calc
    S.rho b = Point3.zero := hr
    _ = S.rho g := (fullSupport_return_eq_zero S hg hfull).symm

theorem pair23_return_ne_zero_of_fullSupport (S : CyclicStaircase) {g b : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g)
    (hb : MinimalComplement S.D b) (hp : Pair23 b) : S.rho b ≠ Point3.zero := by
  have hbg : b ≠ g := by
    intro h
    subst g
    have := hfull.1
    rw [hp.1] at this
    omega
  have hne := return_ne_of_support_inter S hb hg hbg
    (Or.inr (Or.inl ⟨hp.2.1, hfull.2.1⟩))
  intro hr
  apply hne
  calc
    S.rho b = Point3.zero := hr
    _ = S.rho g := (fullSupport_return_eq_zero S hg hfull).symm

private theorem pair12Return_axis_mem (S : CyclicStaircase) (b : Pair12Boundary S) :
    Point3.mk 0 0 (pair12ReturnCoord S b) ∈ S.D := by
  have heq : S.rho b.1 = Point3.mk 0 0 (pair12ReturnCoord S b) := by
    apply Point3.ext
    · exact complementFaceReturn₁ S b.2.1 b.2.2.1
    · exact complementFaceReturn₂ S b.2.1 b.2.2.2.1
    · rfl
  rw [← heq]
  exact S.rho_mem b.1

private theorem pair13Return_axis_mem (S : CyclicStaircase) (b : Pair13Boundary S) :
    Point3.mk 0 (pair13ReturnCoord S b) 0 ∈ S.D := by
  have heq : S.rho b.1 = Point3.mk 0 (pair13ReturnCoord S b) 0 := by
    apply Point3.ext
    · exact complementFaceReturn₁ S b.2.1 b.2.2.1
    · rfl
    · exact complementFaceReturn₃ S b.2.1 b.2.2.2.2
  rw [← heq]
  exact S.rho_mem b.1

private theorem pair23Return_axis_mem (S : CyclicStaircase) (b : Pair23Boundary S) :
    Point3.mk (pair23ReturnCoord S b) 0 0 ∈ S.D := by
  have heq : S.rho b.1 = Point3.mk (pair23ReturnCoord S b) 0 0 := by
    apply Point3.ext
    · rfl
    · exact complementFaceReturn₂ S b.2.1 b.2.2.2.1
    · exact complementFaceReturn₃ S b.2.1 b.2.2.2.2
  rw [← heq]
  exact S.rho_mem b.1

theorem pair12_return_capacity (S : CyclicStaircase) :
    pair12Count S.D ≤ pure3Intercept S := by
  let f : Pair12Boundary S → Fin (pure3Intercept S) := fun b =>
    ⟨pair12ReturnCoord S b, (pure3_axis_mem_iff S _).mp (pair12Return_axis_mem S b)⟩
  have hf : Function.Injective f := by
    intro b c h
    apply pair12ReturnCoord_injective S
    exact congrArg Fin.val h
  simpa using Fintype.card_le_of_injective f hf

theorem pair13_return_capacity (S : CyclicStaircase) :
    pair13Count S.D ≤ pure2Intercept S := by
  let f : Pair13Boundary S → Fin (pure2Intercept S) := fun b =>
    ⟨pair13ReturnCoord S b, (pure2_axis_mem_iff S _).mp (pair13Return_axis_mem S b)⟩
  have hf : Function.Injective f := by
    intro b c h
    apply pair13ReturnCoord_injective S
    exact congrArg Fin.val h
  simpa using Fintype.card_le_of_injective f hf

theorem pair23_return_capacity (S : CyclicStaircase) :
    pair23Count S.D ≤ pure1Intercept S := by
  let f : Pair23Boundary S → Fin (pure1Intercept S) := fun b =>
    ⟨pair23ReturnCoord S b, (pure1_axis_mem_iff S _).mp (pair23Return_axis_mem S b)⟩
  have hf : Function.Injective f := by
    intro b c h
    apply pair23ReturnCoord_injective S
    exact congrArg Fin.val h
  simpa using Fintype.card_le_of_injective f hf

theorem pair12_return_capacity_fullSupport (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    pair12Count S.D + 1 ≤ pure3Intercept S := by
  classical
  have hcoord (b : Pair12Boundary S) : pair12ReturnCoord S b ∈
      Finset.Ico 1 (pure3Intercept S) := by
    rw [Finset.mem_Ico]
    refine ⟨?_, (pure3_axis_mem_iff S _).mp (pair12Return_axis_mem S b)⟩
    have hne := pair12_return_ne_zero_of_fullSupport S hg hfull b.2.1 b.2.2
    by_contra hnot
    have hz : pair12ReturnCoord S b = 0 := Nat.eq_zero_of_not_pos hnot
    apply hne
    apply Point3.ext
    · simpa [Point3.zero] using complementFaceReturn₁ S b.2.1 b.2.2.1
    · simpa [Point3.zero] using complementFaceReturn₂ S b.2.1 b.2.2.2.1
    · simpa [Point3.zero, pair12ReturnCoord] using hz
  let f : Pair12Boundary S →
      {c : ℕ // c ∈ Finset.Ico 1 (pure3Intercept S)} := fun b =>
    ⟨pair12ReturnCoord S b, hcoord b⟩
  let _ : Fintype {c : ℕ // c ∈ Finset.Ico 1 (pure3Intercept S)} :=
    Fintype.ofFinite _
  have hf : Function.Injective f := by
    intro b c h
    apply pair12ReturnCoord_injective S
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  have htarget : Fintype.card {c : ℕ // c ∈ Finset.Ico 1 (pure3Intercept S)} =
      pure3Intercept S - 1 := by simp
  rw [card_pair12Boundary, htarget] at hcard
  have hpos : 0 < pure3Intercept S := (pure3Intercept_pure S).2.2
  omega

theorem pair13_return_capacity_fullSupport (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    pair13Count S.D + 1 ≤ pure2Intercept S := by
  classical
  have hcoord (b : Pair13Boundary S) : pair13ReturnCoord S b ∈
      Finset.Ico 1 (pure2Intercept S) := by
    rw [Finset.mem_Ico]
    refine ⟨?_, (pure2_axis_mem_iff S _).mp (pair13Return_axis_mem S b)⟩
    have hne := pair13_return_ne_zero_of_fullSupport S hg hfull b.2.1 b.2.2
    by_contra hnot
    have hz : pair13ReturnCoord S b = 0 := Nat.eq_zero_of_not_pos hnot
    apply hne
    apply Point3.ext
    · simpa [Point3.zero] using complementFaceReturn₁ S b.2.1 b.2.2.1
    · simpa [Point3.zero, pair13ReturnCoord] using hz
    · simpa [Point3.zero] using complementFaceReturn₃ S b.2.1 b.2.2.2.2
  let f : Pair13Boundary S →
      {c : ℕ // c ∈ Finset.Ico 1 (pure2Intercept S)} := fun b =>
    ⟨pair13ReturnCoord S b, hcoord b⟩
  let _ : Fintype {c : ℕ // c ∈ Finset.Ico 1 (pure2Intercept S)} :=
    Fintype.ofFinite _
  have hf : Function.Injective f := by
    intro b c h
    apply pair13ReturnCoord_injective S
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  have htarget : Fintype.card {c : ℕ // c ∈ Finset.Ico 1 (pure2Intercept S)} =
      pure2Intercept S - 1 := by simp
  rw [card_pair13Boundary, htarget] at hcard
  have hpos : 0 < pure2Intercept S := (pure2Intercept_pure S).2.1
  omega

theorem pair23_return_capacity_fullSupport (S : CyclicStaircase) {g : Point3}
    (hg : MinimalComplement S.D g) (hfull : FullSupport g) :
    pair23Count S.D + 1 ≤ pure1Intercept S := by
  classical
  have hcoord (b : Pair23Boundary S) : pair23ReturnCoord S b ∈
      Finset.Ico 1 (pure1Intercept S) := by
    rw [Finset.mem_Ico]
    refine ⟨?_, (pure1_axis_mem_iff S _).mp (pair23Return_axis_mem S b)⟩
    have hne := pair23_return_ne_zero_of_fullSupport S hg hfull b.2.1 b.2.2
    by_contra hnot
    have hz : pair23ReturnCoord S b = 0 := Nat.eq_zero_of_not_pos hnot
    apply hne
    apply Point3.ext
    · simpa [Point3.zero, pair23ReturnCoord] using hz
    · simpa [Point3.zero] using complementFaceReturn₂ S b.2.1 b.2.2.2.1
    · simpa [Point3.zero] using complementFaceReturn₃ S b.2.1 b.2.2.2.2
  let f : Pair23Boundary S →
      {c : ℕ // c ∈ Finset.Ico 1 (pure1Intercept S)} := fun b =>
    ⟨pair23ReturnCoord S b, hcoord b⟩
  let _ : Fintype {c : ℕ // c ∈ Finset.Ico 1 (pure1Intercept S)} :=
    Fintype.ofFinite _
  have hf : Function.Injective f := by
    intro b c h
    apply pair23ReturnCoord_injective S
    exact congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hf
  have htarget : Fintype.card {c : ℕ // c ∈ Finset.Ico 1 (pure1Intercept S)} =
      pure1Intercept S - 1 := by simp
  rw [card_pair23Boundary, htarget] at hcard
  have hpos : 0 < pure1Intercept S := (pure1Intercept_pure S).1
  omega

theorem pair12_intercept1_lower (S : CyclicStaircase) :
    pair12Count S.D + 1 ≤ pure1Intercept S :=
  pair12_pure1_intercept_lower S.down_closed
    (pure1Intercept_minimalComplement S) (pure1Intercept_pure S)

theorem pair12_intercept2_lower (S : CyclicStaircase) :
    pair12Count S.D + 1 ≤ pure2Intercept S :=
  pair12_pure2_intercept_lower S.down_closed
    (pure2Intercept_minimalComplement S) (pure2Intercept_pure S)

theorem pair13_intercept1_lower (S : CyclicStaircase) :
    pair13Count S.D + 1 ≤ pure1Intercept S :=
  pair13_pure1_intercept_lower S.down_closed
    (pure1Intercept_minimalComplement S) (pure1Intercept_pure S)

theorem pair13_intercept3_lower (S : CyclicStaircase) :
    pair13Count S.D + 1 ≤ pure3Intercept S :=
  pair13_pure3_intercept_lower S.down_closed
    (pure3Intercept_minimalComplement S) (pure3Intercept_pure S)

theorem pair23_intercept2_lower (S : CyclicStaircase) :
    pair23Count S.D + 1 ≤ pure2Intercept S :=
  pair23_pure2_intercept_lower S.down_closed
    (pure2Intercept_minimalComplement S) (pure2Intercept_pure S)

theorem pair23_intercept3_lower (S : CyclicStaircase) :
    pair23Count S.D + 1 ≤ pure3Intercept S :=
  pair23_pure3_intercept_lower S.down_closed
    (pure3Intercept_minimalComplement S) (pure3Intercept_pure S)

end NSP3
