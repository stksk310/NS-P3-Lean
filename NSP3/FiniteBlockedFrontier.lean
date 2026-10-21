import NSP3.FiniteUnitScaling

namespace NSP3

/-- A minimal complement with an already-used residue is permanently absent
from every residue-injective extension. Its predecessors remain present. -/
theorem blocked_minimalComplement_persists {m : ℕ} (w : ResidueWeights m)
    {A D : Finset Point3} (hsub : A ⊆ D) (hinj : residueInjectiveOn D w)
    {b : Point3} (hb : MinimalComplement A b)
    (hused : residueWithWeights w b ∈ A.image (residueWithWeights w)) :
    MinimalComplement D b := by
  have hi : Set.InjOn (residueWithWeights w) (D : Set Point3) :=
    Finset.card_image_iff.mp hinj
  rcases Finset.mem_image.mp hused with ⟨a, ha, heq⟩
  refine ⟨?_, fun hx => hsub (hb.pred1_mem hx),
    fun hy => hsub (hb.pred2_mem hy), fun hz => hsub (hb.pred3_mem hz)⟩
  intro hbd
  have hab : a = b := hi (hsub ha) hbd heq
  exact hb.not_mem (hab ▸ ha)

def blockedPair12 {m : ℕ} (w : ResidueWeights m) (A : Finset Point3) : Finset Point3 :=
  (checkerPair12Boundaries A).filter fun b =>
    residueWithWeights w b ∈ A.image (residueWithWeights w)

def blockedPair13 {m : ℕ} (w : ResidueWeights m) (A : Finset Point3) : Finset Point3 :=
  (checkerPair13Boundaries A).filter fun b =>
    residueWithWeights w b ∈ A.image (residueWithWeights w)

def blockedPair23 {m : ℕ} (w : ResidueWeights m) (A : Finset Point3) : Finset Point3 :=
  (checkerPair23Boundaries A).filter fun b =>
    residueWithWeights w b ∈ A.image (residueWithWeights w)

theorem blockedPair12_subset_terminal {m : ℕ} (w : ResidueWeights m)
    {A D : Finset Point3} (hsub : A ⊆ D) (hinj : residueInjectiveOn D w) :
    blockedPair12 w A ⊆ checkerPair12Boundaries D := by
  intro b hb
  rcases Finset.mem_filter.mp hb with ⟨hbA, hused⟩
  rw [checkerPair12Boundaries_eq, mem_pair12Boundaries] at hbA ⊢
  exact ⟨blocked_minimalComplement_persists w hsub hinj hbA.1 hused, hbA.2⟩

theorem blockedPair13_subset_terminal {m : ℕ} (w : ResidueWeights m)
    {A D : Finset Point3} (hsub : A ⊆ D) (hinj : residueInjectiveOn D w) :
    blockedPair13 w A ⊆ checkerPair13Boundaries D := by
  intro b hb
  rcases Finset.mem_filter.mp hb with ⟨hbA, hused⟩
  rw [checkerPair13Boundaries_eq, mem_pair13Boundaries] at hbA ⊢
  exact ⟨blocked_minimalComplement_persists w hsub hinj hbA.1 hused, hbA.2⟩

theorem blockedPair23_subset_terminal {m : ℕ} (w : ResidueWeights m)
    {A D : Finset Point3} (hsub : A ⊆ D) (hinj : residueInjectiveOn D w) :
    blockedPair23 w A ⊆ checkerPair23Boundaries D := by
  intro b hb
  rcases Finset.mem_filter.mp hb with ⟨hbA, hused⟩
  rw [checkerPair23Boundaries_eq, mem_pair23Boundaries] at hbA ⊢
  exact ⟨blocked_minimalComplement_persists w hsub hinj hbA.1 hused, hbA.2⟩

/-- All three permanent-count obstructions are sound terminal rejection rules. -/
theorem no_terminal_of_blocked_pair_excess {m : ℕ} (w : ResidueWeights m)
    {A D : Finset Point3} (hsub : A ⊆ D) (hinj : residueInjectiveOn D w)
    (q : FullResidualTuple) (g : Point3)
    (hexcess : q.r < (blockedPair12 w A).card ∨
      q.s < (blockedPair13 w A).card ∨ q.t < (blockedPair23 w A).card) :
    ¬ terminalMatches q m g D := by
  intro ht
  have h12 := Finset.card_le_card (blockedPair12_subset_terminal w hsub hinj)
  have h13 := Finset.card_le_card (blockedPair13_subset_terminal w hsub hinj)
  have h23 := Finset.card_le_card (blockedPair23_subset_terminal w hsub hinj)
  rcases ht with ⟨_, _, _, hqr, hqs, hqt⟩
  change (checkerPair12Boundaries D).card = q.r at hqr
  change (checkerPair13Boundaries D).card = q.s at hqs
  change (checkerPair23Boundaries D).card = q.t at hqt
  rcases hexcess with h | h | h <;> omega

end NSP3
