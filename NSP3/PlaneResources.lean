import NSP3.NoFullResources

namespace NSP3

noncomputable def plane12PosFinset (S : CyclicStaircase) : Finset Point3 := by
  classical
  exact S.D.filter fun p => 0 < p.x ∧ 0 < p.y ∧ p.z = 0

noncomputable def plane13PosFinset (S : CyclicStaircase) : Finset Point3 := by
  classical
  exact S.D.filter fun p => 0 < p.x ∧ p.y = 0 ∧ 0 < p.z

noncomputable def plane23PosFinset (S : CyclicStaircase) : Finset Point3 := by
  classical
  exact S.D.filter fun p => p.x = 0 ∧ 0 < p.y ∧ 0 < p.z

@[simp] theorem mem_plane12PosFinset (S : CyclicStaircase) (p : Point3) :
    p ∈ plane12PosFinset S ↔ p ∈ S.D ∧ 0 < p.x ∧ 0 < p.y ∧ p.z = 0 := by
  simp [plane12PosFinset]

@[simp] theorem mem_plane13PosFinset (S : CyclicStaircase) (p : Point3) :
    p ∈ plane13PosFinset S ↔ p ∈ S.D ∧ 0 < p.x ∧ p.y = 0 ∧ 0 < p.z := by
  simp [plane13PosFinset]

@[simp] theorem mem_plane23PosFinset (S : CyclicStaircase) (p : Point3) :
    p ∈ plane23PosFinset S ↔ p ∈ S.D ∧ p.x = 0 ∧ 0 < p.y ∧ 0 < p.z := by
  simp [plane23PosFinset]

private def pair12TrianglePoint (i : ℕ × ℕ) : Point3 :=
  ⟨i.1 + 1, i.2 - i.1, 0⟩

private def pair13TrianglePoint (i : ℕ × ℕ) : Point3 :=
  ⟨i.1 + 1, 0, i.2 - i.1⟩

private def pair23TrianglePoint (i : ℕ × ℕ) : Point3 :=
  ⟨0, i.1 + 1, i.2 - i.1⟩

private noncomputable def pair12TriangleFinset (S : CyclicStaircase) : Finset Point3 := by
  classical
  exact (pairTriangleIndices (pair12Count S.D)).image pair12TrianglePoint

private noncomputable def pair13TriangleFinset (S : CyclicStaircase) : Finset Point3 := by
  classical
  exact (pairTriangleIndices (pair13Count S.D)).image pair13TrianglePoint

private noncomputable def pair23TriangleFinset (S : CyclicStaircase) : Finset Point3 := by
  classical
  exact (pairTriangleIndices (pair23Count S.D)).image pair23TrianglePoint

private theorem mem_pair12TriangleFinset (S : CyclicStaircase) (p : Point3) :
    p ∈ pair12TriangleFinset S ↔
      0 < p.x ∧ 0 < p.y ∧ p.z = 0 ∧ p.x + p.y ≤ pair12Count S.D := by
  classical
  constructor
  · rintro hp
    obtain ⟨i, hi_mem, rfl⟩ := Finset.mem_image.mp hp
    have hi := (Finset.mem_filter.mp hi_mem).2
    have hir := Finset.mem_product.mp (Finset.mem_filter.mp hi_mem).1
    have hj : i.2 < pair12Count S.D := Finset.mem_range.mp hir.2
    simp [pair12TrianglePoint]
    omega
  · rintro ⟨hx, hy, hz, hsum⟩
    let i : ℕ × ℕ := (p.x - 1, p.x + p.y - 1)
    have hi_mem : i ∈ pairTriangleIndices (pair12Count S.D) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, ?_⟩
      · dsimp [i]; omega
      · dsimp [i]; omega
      · dsimp [i]; omega
    apply Finset.mem_image.mpr
    refine ⟨i, hi_mem, ?_⟩
    apply Point3.ext <;> simp [pair12TrianglePoint, i, hz] <;> omega

private theorem mem_pair13TriangleFinset (S : CyclicStaircase) (p : Point3) :
    p ∈ pair13TriangleFinset S ↔
      0 < p.x ∧ p.y = 0 ∧ 0 < p.z ∧ p.x + p.z ≤ pair13Count S.D := by
  classical
  constructor
  · rintro hp
    obtain ⟨i, hi_mem, rfl⟩ := Finset.mem_image.mp hp
    have hi := (Finset.mem_filter.mp hi_mem).2
    have hir := Finset.mem_product.mp (Finset.mem_filter.mp hi_mem).1
    have hj : i.2 < pair13Count S.D := Finset.mem_range.mp hir.2
    simp [pair13TrianglePoint]
    omega
  · rintro ⟨hx, hy, hz, hsum⟩
    let i : ℕ × ℕ := (p.x - 1, p.x + p.z - 1)
    have hi_mem : i ∈ pairTriangleIndices (pair13Count S.D) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, ?_⟩
      · dsimp [i]; omega
      · dsimp [i]; omega
      · dsimp [i]; omega
    apply Finset.mem_image.mpr
    refine ⟨i, hi_mem, ?_⟩
    apply Point3.ext <;> simp [pair13TrianglePoint, i, hy] <;> omega

private theorem mem_pair23TriangleFinset (S : CyclicStaircase) (p : Point3) :
    p ∈ pair23TriangleFinset S ↔
      p.x = 0 ∧ 0 < p.y ∧ 0 < p.z ∧ p.y + p.z ≤ pair23Count S.D := by
  classical
  constructor
  · rintro hp
    obtain ⟨i, hi_mem, rfl⟩ := Finset.mem_image.mp hp
    have hi := (Finset.mem_filter.mp hi_mem).2
    have hir := Finset.mem_product.mp (Finset.mem_filter.mp hi_mem).1
    have hj : i.2 < pair23Count S.D := Finset.mem_range.mp hir.2
    simp [pair23TrianglePoint]
    omega
  · rintro ⟨hx, hy, hz, hsum⟩
    let i : ℕ × ℕ := (p.y - 1, p.y + p.z - 1)
    have hi_mem : i ∈ pairTriangleIndices (pair23Count S.D) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, ?_⟩
      · dsimp [i]; omega
      · dsimp [i]; omega
      · dsimp [i]; omega
    apply Finset.mem_image.mpr
    refine ⟨i, hi_mem, ?_⟩
    apply Point3.ext <;> simp [pair23TrianglePoint, i, hx] <;> omega

noncomputable def pair12ExtraFinset (S : CyclicStaircase) : Finset Point3 :=
  plane12PosFinset S \ pair12TriangleFinset S

noncomputable def pair13ExtraFinset (S : CyclicStaircase) : Finset Point3 :=
  plane13PosFinset S \ pair13TriangleFinset S

noncomputable def pair23ExtraFinset (S : CyclicStaircase) : Finset Point3 :=
  plane23PosFinset S \ pair23TriangleFinset S

@[simp] theorem mem_pair12ExtraFinset (S : CyclicStaircase) (p : Point3) :
    p ∈ pair12ExtraFinset S ↔
      p ∈ S.D ∧ 0 < p.x ∧ 0 < p.y ∧ p.z = 0 ∧ pair12Count S.D < p.x + p.y := by
  simp only [pair12ExtraFinset, Finset.mem_sdiff, mem_plane12PosFinset,
    mem_pair12TriangleFinset]
  constructor
  · rintro ⟨⟨hD, hx, hy, hz⟩, hnot⟩
    refine ⟨hD, hx, hy, hz, Nat.lt_of_not_ge ?_⟩
    exact fun hle => hnot ⟨hx, hy, hz, hle⟩
  · rintro ⟨hD, hx, hy, hz, hlt⟩
    refine ⟨⟨hD, hx, hy, hz⟩, ?_⟩
    rintro ⟨-, -, -, hle⟩
    omega

@[simp] theorem mem_pair13ExtraFinset (S : CyclicStaircase) (p : Point3) :
    p ∈ pair13ExtraFinset S ↔
      p ∈ S.D ∧ 0 < p.x ∧ p.y = 0 ∧ 0 < p.z ∧ pair13Count S.D < p.x + p.z := by
  simp only [pair13ExtraFinset, Finset.mem_sdiff, mem_plane13PosFinset,
    mem_pair13TriangleFinset]
  constructor
  · rintro ⟨⟨hD, hx, hy, hz⟩, hnot⟩
    refine ⟨hD, hx, hy, hz, Nat.lt_of_not_ge ?_⟩
    exact fun hle => hnot ⟨hx, hy, hz, hle⟩
  · rintro ⟨hD, hx, hy, hz, hlt⟩
    refine ⟨⟨hD, hx, hy, hz⟩, ?_⟩
    rintro ⟨-, -, -, hle⟩
    omega

@[simp] theorem mem_pair23ExtraFinset (S : CyclicStaircase) (p : Point3) :
    p ∈ pair23ExtraFinset S ↔
      p ∈ S.D ∧ p.x = 0 ∧ 0 < p.y ∧ 0 < p.z ∧ pair23Count S.D < p.y + p.z := by
  simp only [pair23ExtraFinset, Finset.mem_sdiff, mem_plane23PosFinset,
    mem_pair23TriangleFinset]
  constructor
  · rintro ⟨⟨hD, hx, hy, hz⟩, hnot⟩
    refine ⟨hD, hx, hy, hz, Nat.lt_of_not_ge ?_⟩
    exact fun hle => hnot ⟨hx, hy, hz, hle⟩
  · rintro ⟨hD, hx, hy, hz, hlt⟩
    refine ⟨⟨hD, hx, hy, hz⟩, ?_⟩
    rintro ⟨-, -, -, hle⟩
    omega

private theorem pair12TriangleFinset_subset (S : CyclicStaircase) :
    pair12TriangleFinset S ⊆ plane12PosFinset S := by
  intro p hp
  rcases (mem_pair12TriangleFinset S p).mp hp with ⟨hx, hy, hz, hsum⟩
  apply (mem_plane12PosFinset S p).mpr
  have hmem : Point3.mk p.x p.y 0 ∈ S.D :=
    pair12Triangle_subset S.down_closed hx hy hsum
  have heq : Point3.mk p.x p.y 0 = p := by ext <;> simp [hz]
  exact ⟨heq ▸ hmem, hx, hy, hz⟩

private theorem pair13TriangleFinset_subset (S : CyclicStaircase) :
    pair13TriangleFinset S ⊆ plane13PosFinset S := by
  intro p hp
  rcases (mem_pair13TriangleFinset S p).mp hp with ⟨hx, hy, hz, hsum⟩
  apply (mem_plane13PosFinset S p).mpr
  have hmem : Point3.mk p.x 0 p.z ∈ S.D :=
    pair13Triangle_subset S.down_closed hx hz hsum
  have heq : Point3.mk p.x 0 p.z = p := by ext <;> simp [hy]
  exact ⟨heq ▸ hmem, hx, hy, hz⟩

private theorem pair23TriangleFinset_subset (S : CyclicStaircase) :
    pair23TriangleFinset S ⊆ plane23PosFinset S := by
  intro p hp
  rcases (mem_pair23TriangleFinset S p).mp hp with ⟨hx, hy, hz, hsum⟩
  apply (mem_plane23PosFinset S p).mpr
  have hmem : Point3.mk 0 p.y p.z ∈ S.D :=
    pair23Triangle_subset S.down_closed hy hz hsum
  have heq : Point3.mk 0 p.y p.z = p := by ext <;> simp [hx]
  exact ⟨heq ▸ hmem, hx, hy, hz⟩

private theorem card_pair12TriangleFinset (S : CyclicStaircase) :
    (pair12TriangleFinset S).card = Nat.choose (pair12Count S.D) 2 := by
  classical
  rw [pair12TriangleFinset, Finset.card_image_iff.mpr]
  · exact card_pairTriangleIndices _
  · intro a ha b hb h
    apply Prod.ext
    · simpa [pair12TrianglePoint] using congrArg Point3.x h
    · have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hx := congrArg Point3.x h
      have hy := congrArg Point3.y h
      simp [pair12TrianglePoint] at hx hy
      omega

private theorem card_pair13TriangleFinset (S : CyclicStaircase) :
    (pair13TriangleFinset S).card = Nat.choose (pair13Count S.D) 2 := by
  classical
  rw [pair13TriangleFinset, Finset.card_image_iff.mpr]
  · exact card_pairTriangleIndices _
  · intro a ha b hb h
    apply Prod.ext
    · simpa [pair13TrianglePoint] using congrArg Point3.x h
    · have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hx := congrArg Point3.x h
      have hz := congrArg Point3.z h
      simp [pair13TrianglePoint] at hx hz
      omega

private theorem card_pair23TriangleFinset (S : CyclicStaircase) :
    (pair23TriangleFinset S).card = Nat.choose (pair23Count S.D) 2 := by
  classical
  rw [pair23TriangleFinset, Finset.card_image_iff.mpr]
  · exact card_pairTriangleIndices _
  · intro a ha b hb h
    apply Prod.ext
    · simpa [pair23TrianglePoint] using congrArg Point3.y h
    · have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hy := congrArg Point3.y h
      have hz := congrArg Point3.z h
      simp [pair23TrianglePoint] at hy hz
      omega

theorem card_plane12PosFinset (S : CyclicStaircase) :
    (plane12PosFinset S).card =
      Nat.choose (pair12Count S.D) 2 + (pair12ExtraFinset S).card := by
  have h := Finset.card_sdiff_add_card_eq_card (pair12TriangleFinset_subset S)
  rw [card_pair12TriangleFinset] at h
  unfold pair12ExtraFinset
  omega

theorem card_plane13PosFinset (S : CyclicStaircase) :
    (plane13PosFinset S).card =
      Nat.choose (pair13Count S.D) 2 + (pair13ExtraFinset S).card := by
  have h := Finset.card_sdiff_add_card_eq_card (pair13TriangleFinset_subset S)
  rw [card_pair13TriangleFinset] at h
  unfold pair13ExtraFinset
  omega

theorem card_plane23PosFinset (S : CyclicStaircase) :
    (plane23PosFinset S).card =
      Nat.choose (pair23Count S.D) 2 + (pair23ExtraFinset S).card := by
  have h := Finset.card_sdiff_add_card_eq_card (pair23TriangleFinset_subset S)
  rw [card_pair23TriangleFinset] at h
  unfold pair23ExtraFinset
  omega

theorem pair12PlaneExact_of_extra_card_eq_zero (S : CyclicStaircase)
    (hzero : (pair12ExtraFinset S).card = 0) : Pair12PlaneExact S := by
  intro x y hx hy
  constructor
  · intro hmem
    by_contra hnot
    have hlarge : pair12Count S.D < x + y := Nat.lt_of_not_ge hnot
    have hextra : Point3.mk x y 0 ∈ pair12ExtraFinset S :=
      (mem_pair12ExtraFinset S _).mpr ⟨hmem, hx, hy, rfl, by simpa using hlarge⟩
    have hpos : 0 < (pair12ExtraFinset S).card := Finset.card_pos.mpr ⟨_, hextra⟩
    omega
  · exact pair12Triangle_subset S.down_closed hx hy

theorem pair13PlaneExact_of_extra_card_eq_zero (S : CyclicStaircase)
    (hzero : (pair13ExtraFinset S).card = 0) : Pair13PlaneExact S := by
  intro x z hx hz
  constructor
  · intro hmem
    by_contra hnot
    have hlarge : pair13Count S.D < x + z := Nat.lt_of_not_ge hnot
    have hextra : Point3.mk x 0 z ∈ pair13ExtraFinset S :=
      (mem_pair13ExtraFinset S _).mpr ⟨hmem, hx, rfl, hz, by simpa using hlarge⟩
    have hpos : 0 < (pair13ExtraFinset S).card := Finset.card_pos.mpr ⟨_, hextra⟩
    omega
  · exact pair13Triangle_subset S.down_closed hx hz

theorem pair23PlaneExact_of_extra_card_eq_zero (S : CyclicStaircase)
    (hzero : (pair23ExtraFinset S).card = 0) : Pair23PlaneExact S := by
  intro y z hy hz
  constructor
  · intro hmem
    by_contra hnot
    have hlarge : pair23Count S.D < y + z := Nat.lt_of_not_ge hnot
    have hextra : Point3.mk 0 y z ∈ pair23ExtraFinset S :=
      (mem_pair23ExtraFinset S _).mpr ⟨hmem, rfl, hy, hz, by simpa using hlarge⟩
    have hpos : 0 < (pair23ExtraFinset S).card := Finset.card_pos.mpr ⟨_, hextra⟩
    omega
  · exact pair23Triangle_subset S.down_closed hy hz

theorem pair12Extra_card_pos_of_not_exact (S : CyclicStaircase)
    (hnot : ¬ Pair12PlaneExact S) : 1 ≤ (pair12ExtraFinset S).card := by
  by_contra h
  exact hnot (pair12PlaneExact_of_extra_card_eq_zero S (by omega))

theorem pair13Extra_card_pos_of_not_exact (S : CyclicStaircase)
    (hnot : ¬ Pair13PlaneExact S) : 1 ≤ (pair13ExtraFinset S).card := by
  by_contra h
  exact hnot (pair13PlaneExact_of_extra_card_eq_zero S (by omega))

theorem pair23Extra_card_pos_of_not_exact (S : CyclicStaircase)
    (hnot : ¬ Pair23PlaneExact S) : 1 ≤ (pair23ExtraFinset S).card := by
  by_contra h
  exact hnot (pair23PlaneExact_of_extra_card_eq_zero S (by omega))

end NSP3
