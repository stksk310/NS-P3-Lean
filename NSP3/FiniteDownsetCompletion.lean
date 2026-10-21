import NSP3.FiniteResidueWeights

namespace NSP3

def pointRank (p : Point3) : ℕ := p.x + p.y + p.z

/-- Computable strict coordinatewise lower box. -/
def strictLowerBox (p : Point3) : Finset Point3 :=
  (pointBox (p.x + p.y + p.z + 1)).filter fun q =>
    q.x ≤ p.x ∧ q.y ≤ p.y ∧ q.z ≤ p.z ∧ q ≠ p

@[simp] theorem mem_strictLowerBox (p q : Point3) :
    q ∈ strictLowerBox p ↔ q ≤ p ∧ q ≠ p := by
  constructor
  · intro h
    rcases Finset.mem_filter.mp h with ⟨_, hx, hy, hz, hne⟩
    exact ⟨⟨hx, hy, hz⟩, hne⟩
  · rintro ⟨⟨hx, hy, hz⟩, hne⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_pointBox _ _).mpr ⟨by omega, by omega, by omega⟩,
      hx, hy, hz, hne⟩

/-- Every admissible one-point downset extension.  `lowerBoxFinset p` is the
exact set of strict coordinatewise predecessors of `p`. -/
def extensionCandidates {m : ℕ} (bound : ℕ) (w : ResidueWeights m)
    (A : Finset Point3) : Finset Point3 :=
  (pointBox bound).filter fun p =>
    p ∉ A ∧ strictLowerBox p ⊆ A ∧
      residueWithWeights w p ∉ A.image (residueWithWeights w)

@[simp] theorem mem_extensionCandidates {m : ℕ} (bound : ℕ)
    (w : ResidueWeights m) (A : Finset Point3) (p : Point3) :
    p ∈ extensionCandidates bound w A ↔
      p ∈ pointBox bound ∧ p ∉ A ∧ strictLowerBox p ⊆ A ∧
        residueWithWeights w p ∉ A.image (residueWithWeights w) := by
  simp [extensionCandidates, and_assoc]

theorem insert_isDownset_of_mem_extensionCandidates {m bound : ℕ}
    {w : ResidueWeights m} {A : Finset Point3} (hA : IsDownset A) {p : Point3}
    (hp : p ∈ extensionCandidates bound w A) : IsDownset (insert p A) := by
  intro a b hab hb
  rw [Finset.mem_insert] at hb ⊢
  rcases hb with hbp | hbA
  · subst b
    by_cases hap : a = p
    · exact Or.inl hap
    · rcases (mem_extensionCandidates _ _ _ _).mp hp with
        ⟨_, _, hpred, _⟩
      exact Or.inr (hpred ((mem_strictLowerBox p a).mpr ⟨hab, hap⟩))
  · exact Or.inr (hA.mem_of_le hab hbA)

/-- Coverage of one completion step: a proper downset subset of an actual
bounded residue-injective downset always has an enumerated next point. -/
theorem exists_actual_extensionCandidate {m : ℕ} (w : ResidueWeights m)
    {A D : Finset Point3}
    (hA : IsDownset A) (hD : IsDownset D) (hsub : A ⊆ D)
    (hbound : D ⊆ pointBox m) (hinj : residueInjectiveOn D w)
    (hcard : A.card < D.card) :
    ∃ p ∈ extensionCandidates m w A, p ∈ D := by
  have hnot : ¬ D ⊆ A := by
    intro hDA
    have heq : A = D := Finset.Subset.antisymm hsub hDA
    have hcards := congrArg Finset.card heq
    omega
  rcases Finset.not_subset.mp hnot with ⟨p0, hp0D, hp0A⟩
  have hdiff : (D \ A).Nonempty :=
    ⟨p0, Finset.mem_sdiff.mpr ⟨hp0D, hp0A⟩⟩
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image (D \ A) pointRank hdiff
  have hpD : p ∈ D := (Finset.mem_sdiff.mp hp).1
  have hpA : p ∉ A := (Finset.mem_sdiff.mp hp).2
  refine ⟨p, (mem_extensionCandidates m w A p).mpr ⟨hbound hpD, hpA, ?_, ?_⟩,
    hpD⟩
  · intro q hq
    have hqp := (mem_strictLowerBox p q).mp hq
    have hqD : q ∈ D := hD.mem_of_le hqp.1 hpD
    by_contra hqA
    have hqdiff : q ∈ D \ A := Finset.mem_sdiff.mpr ⟨hqD, hqA⟩
    have hle := hmin q hqdiff
    rcases hqp.1 with ⟨hx, hy, hz⟩
    have hlt : pointRank q < pointRank p := by
      unfold pointRank
      have hcoord : q.x ≠ p.x ∨ q.y ≠ p.y ∨ q.z ≠ p.z := by
        by_contra h
        push_neg at h
        apply hqp.2
        ext <;> simp_all
      rcases hcoord with hne | hne | hne <;> omega
    omega
  · intro hres
    rcases Finset.mem_image.mp hres with ⟨a, ha, hap⟩
    have hinj' : Set.InjOn (residueWithWeights w) (D : Set Point3) := by
      exact (Finset.card_image_iff.mp hinj)
    have hpa : p = a := hinj' hpD (hsub ha) hap.symm
    exact hpA (hpa ▸ ha)

/-- Exact finite branching recursion: after `fuel` steps it contains every
set obtainable by repeatedly adjoining an admissible point. -/
def downsetCompletions {m : ℕ} : ℕ → ℕ → ResidueWeights m →
    Finset Point3 → Finset (Finset Point3)
  | 0, _, _, A => {A}
  | fuel + 1, bound, w, A =>
      (extensionCandidates bound w A).biUnion fun p =>
        downsetCompletions fuel bound w (insert p A)

/-- Iterated coverage: after exactly the cardinality gap many branches, the
actual bounded residue-injective downset itself occurs in the recursion. -/
theorem actual_mem_downsetCompletions {m : ℕ} (w : ResidueWeights m)
    (fuel : ℕ) {A D : Finset Point3}
    (hA : IsDownset A) (hD : IsDownset D) (hsub : A ⊆ D)
    (hbound : D ⊆ pointBox m) (hinj : residueInjectiveOn D w)
    (hcard : A.card + fuel = D.card) :
    D ∈ downsetCompletions fuel m w A := by
  induction fuel generalizing A with
  | zero =>
      simp only [Nat.add_zero] at hcard
      have heq : A = D := Finset.eq_of_subset_of_card_le hsub (by omega)
      simp [downsetCompletions, heq]
  | succ fuel ih =>
      have hlt : A.card < D.card := by omega
      obtain ⟨p, hpcand, hpD⟩ :=
        exists_actual_extensionCandidate w hA hD hsub hbound hinj hlt
      have hpA : p ∉ A := (mem_extensionCandidates m w A p).mp hpcand |>.2.1
      have hsub' : insert p A ⊆ D := by
        intro q hq
        rw [Finset.mem_insert] at hq
        rcases hq with hqp | hqA
        · exact hqp ▸ hpD
        · exact hsub hqA
      have hcard' : (insert p A).card + fuel = D.card := by
        rw [Finset.card_insert_of_notMem hpA]
        omega
      have hrec : D ∈ downsetCompletions fuel m w (insert p A) :=
        ih (insert_isDownset_of_mem_extensionCandidates hA hpcand)
          hsub' hcard'
      rw [downsetCompletions]
      exact Finset.mem_biUnion.mpr ⟨p, hpcand, hrec⟩

end NSP3
