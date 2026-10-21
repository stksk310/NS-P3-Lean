import NSP3.PresentationBound

namespace NSP3

/-- Intrinsic positive additive indecomposability in the actual carrier. -/
def SemigroupAtom (S : Set ℕ) (n : ℕ) : Prop :=
  n ∈ S ∧ 0 < n ∧ ∀ x ∈ S, ∀ y ∈ S, n = x+y → x=0 ∨ y=0

def IsSemigroupMultiplicity (S : Set ℕ) (m : ℕ) : Prop :=
  m ∈ S ∧ 0 < m ∧ ∀ n ∈ S, 0 < n → m ≤ n

noncomputable def semigroupEmbeddingDimension (S : Set ℕ) : ℕ :=
  Nat.card {n : ℕ // SemigroupAtom S n}

/-- Minimality is imposed on the inputs; exhaustion, multiplicity and dimension are not fields. -/
structure MinimalFourGeneratorClass (m a b c : ℕ) : Prop where
  distinct : ([m,a,b,c] : List ℕ).Nodup
  positive : 0 < m
  least_a : m ≤ a
  least_b : m ≤ b
  least_c : m ≤ c
  coprime : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1
  atoms : ∀ g ∈ ([m,a,b,c] : List ℕ), SemigroupAtom (generatedSemigroup m a b c) g

theorem semigroupAtom_add_cases (S : Set ℕ) {n x y : ℕ}
    (hn : SemigroupAtom S n) (hx : x ∈ S) (hy : y ∈ S) (he : n=x+y) :
    n=x ∨ n=y := by
  rcases hn.2.2 x hx y hy he with h | h <;> simp_all

theorem semigroupAtom_mul_eq (S : AddSubmonoid ℕ) (g k : ℕ) (hg : g ∈ S)
    (hn : SemigroupAtom (S : Set ℕ) (k*g)) : k*g=g := by
  cases k with
  | zero => simpa using hn.2.1
  | succ k =>
    have hk : k*g ∈ S := by simpa [nsmul_eq_mul] using S.nsmul_mem hg k
    have he : (k+1)*g = g+k*g := by ring
    rcases hn.2.2 g hg (k*g) hk he with hz | hz
    · have : (k+1)*g = 0 := by simp [hz]
      omega
    · omega

/-- Exhaustion follows from an actual nonnegative coefficient representation. -/
theorem generatedSemigroup_atom_exhaustion (m a b c n : ℕ)
    (hn : SemigroupAtom (generatedSemigroup m a b c) n) :
    n ∈ ([m,a,b,c] : List ℕ) := by
  obtain ⟨k,x,y,z,he⟩ := hn.1
  let S := generatedAddSubmonoid m a b c
  have hg := generatedSemigroup_generators m a b c
  have hk : k*m ∈ S := by simpa [nsmul_eq_mul] using S.nsmul_mem hg.1 k
  have hx : a*x ∈ S := by simpa [nsmul_eq_mul, mul_comm] using S.nsmul_mem hg.2.1 x
  have hy : b*y ∈ S := by simpa [nsmul_eq_mul, mul_comm] using S.nsmul_mem hg.2.2.1 y
  have hz : c*z ∈ S := by simpa [nsmul_eq_mul, mul_comm] using S.nsmul_mem hg.2.2.2 z
  rcases semigroupAtom_add_cases _ hn (S.add_mem (S.add_mem hk hx) hy) hz he with he₁ | he₁
  · rcases semigroupAtom_add_cases _ hn (S.add_mem hk hx) hy he₁ with he₂ | he₂
    · rcases semigroupAtom_add_cases _ hn hk hx he₂ with he₃ | he₃
      · have ha : SemigroupAtom (S : Set ℕ) (k*m) := by
          change SemigroupAtom (generatedSemigroup m a b c) (k*m)
          rw [← he₃]; exact hn
        have := semigroupAtom_mul_eq S m k hg.1 ha
        simp [he₃, this]
      · have ha : SemigroupAtom (S : Set ℕ) (x*a) := by
          change SemigroupAtom (generatedSemigroup m a b c) (x*a)
          rw [mul_comm, ← he₃]; exact hn
        have := semigroupAtom_mul_eq S a x hg.2.1 ha
        have heq : n=a := he₃.trans ((Nat.mul_comm a x).trans this)
        simp [heq]
    · have ha : SemigroupAtom (S : Set ℕ) (y*b) := by
        change SemigroupAtom (generatedSemigroup m a b c) (y*b)
        rw [mul_comm, ← he₂]; exact hn
      have := semigroupAtom_mul_eq S b y hg.2.2.1 ha
      have heq : n=b := he₂.trans ((Nat.mul_comm b y).trans this)
      simp [heq]
  · have ha : SemigroupAtom (S : Set ℕ) (z*c) := by
      change SemigroupAtom (generatedSemigroup m a b c) (z*c)
      rw [mul_comm, ← he₁]; exact hn
    have := semigroupAtom_mul_eq S c z hg.2.2.2 ha
    have heq : n=c := he₁.trans ((Nat.mul_comm c z).trans this)
    simp [heq]

theorem minimalFour_atom_iff (m a b c n : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    SemigroupAtom (generatedSemigroup m a b c) n ↔ n ∈ ([m,a,b,c] : List ℕ) :=
  ⟨generatedSemigroup_atom_exhaustion m a b c n, h.atoms n⟩

theorem minimalFour_multiplicity (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    IsSemigroupMultiplicity (generatedSemigroup m a b c) m := by
  refine ⟨(generatedSemigroup_generators m a b c).1, h.positive, ?_⟩
  rintro n ⟨k,x,y,z,he⟩ hn
  have hm := h.positive
  have ha := h.least_a
  have hb := h.least_b
  have hc := h.least_c
  by_cases hk : 0 < k
  · have : m ≤ k*m := Nat.le_mul_of_pos_left m hk
    omega
  by_cases hx : 0 < x
  · have : a ≤ a*x := Nat.le_mul_of_pos_right a hx
    omega
  by_cases hy : 0 < y
  · have : b ≤ b*y := Nat.le_mul_of_pos_right b hy
    omega
  by_cases hz : 0 < z
  · have : c ≤ c*z := Nat.le_mul_of_pos_right c hz
    omega
  have : k=0 ∧ x=0 ∧ y=0 ∧ z=0 := by omega
  simp_all

theorem minimalFour_embeddingDimension (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    semigroupEmbeddingDimension (generatedSemigroup m a b c) = 4 := by
  classical
  have he : {n | SemigroupAtom (generatedSemigroup m a b c) n} =
      (([m,a,b,c] : List ℕ).toFinset : Set ℕ) := by
    ext n
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, List.mem_toFinset]
    exact minimalFour_atom_iff m a b c n h
  change Nat.card {n // n ∈ {n | SemigroupAtom (generatedSemigroup m a b c) n}} = 4
  rw [Nat.card_coe_set_eq, he, Set.ncard_coe_finset, List.toFinset_card_of_nodup h.distinct]
  rfl

theorem minimal_generator_class_bridge (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c) :
    IsSemigroupMultiplicity (generatedSemigroup m a b c) m ∧
    (∀ n, SemigroupAtom (generatedSemigroup m a b c) n ↔ n ∈ ([m,a,b,c] : List ℕ)) ∧
    semigroupEmbeddingDimension (generatedSemigroup m a b c) = 4 ∧
    (generatedSemigroup m a b c)ᶜ.Finite :=
  ⟨minimalFour_multiplicity m a b c h, fun n => minimalFour_atom_iff m a b c n h,
    minimalFour_embeddingDimension m a b c h, generatedSemigroup_cofinite m a b c h.positive h.coprime⟩

end NSP3
