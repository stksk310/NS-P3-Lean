import NSP3.GeneratedSemigroupApery

/-!
Actual semigroup pieces of the V03 Betti argument.

These definitions use membership in the existing generated semigroup, not an
assumed homological certificate. IsPseudoFrobenius concerns nonnegative
pseudo-Frobenius gaps; this is the usual range for the four-generated class.
No theorem here identifies these cardinalities with Tor ranks or asserts the
Scarf corner inequality.
-/

namespace NSP3.V03

/-- A nonnegative gap whose sum with every positive semigroup member is present. -/
def IsPseudoFrobenius (m a b c f : ℕ) : Prop :=
  f ∉ generatedSemigroup m a b c ∧
    ∀ s ∈ generatedSemigroup m a b c, 0 < s →
      f+s ∈ generatedSemigroup m a b c

/-- Testing all four actual generators suffices, since they generate the monoid. -/
theorem isPseudoFrobenius_iff_generators (m a b c f : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsPseudoFrobenius m a b c f ↔
      f ∉ generatedSemigroup m a b c ∧
      f+m ∈ generatedSemigroup m a b c ∧
      f+a ∈ generatedSemigroup m a b c ∧
      f+b ∈ generatedSemigroup m a b c ∧
      f+c ∈ generatedSemigroup m a b c := by
  constructor
  · intro hf
    have hg := generatedSemigroup_generators m a b c
    exact ⟨hf.1, hf.2 m hg.1 hm, hf.2 a hg.2.1 ha,
      hf.2 b hg.2.2.1 hb, hf.2 c hg.2.2.2 hc⟩
  · rintro ⟨hgap, hfm, hfa, hfb, hfc⟩
    refine ⟨hgap, ?_⟩
    rintro s ⟨k,x,y,z,rfl⟩ hs
    by_cases hk : k = 0
    · subst k
      by_cases hx : x = 0
      · subst x
        by_cases hy : y = 0
        · subst y
          have hz : z ≠ 0 := by intro h; simp [h] at hs
          obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
          have hr : j*c ∈ generatedSemigroup m a b c :=
            ⟨0,0,0,j,by ring⟩
          convert generatedSemigroup_add m a b c hfc hr using 1 <;>
            simp only [Nat.succ_eq_add_one] <;> ring
        · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hy
          have hr : b*j+c*z ∈ generatedSemigroup m a b c :=
            ⟨0,0,j,z,by ring⟩
          convert generatedSemigroup_add m a b c hfb hr using 1 <;>
            simp only [Nat.succ_eq_add_one] <;> ring
      · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hx
        have hr : a*j+b*y+c*z ∈ generatedSemigroup m a b c :=
          ⟨0,j,y,z,by ring⟩
        convert generatedSemigroup_add m a b c hfa hr using 1 <;>
          simp only [Nat.succ_eq_add_one] <;> ring
    · obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      have hr : j*m+a*x+b*y+c*z ∈ generatedSemigroup m a b c :=
        ⟨j,x,y,z,rfl⟩
      convert generatedSemigroup_add m a b c hfm hr using 1 <;>
        simp only [Nat.succ_eq_add_one] <;> ring

/-- The three nonmultiplicity generators kill this Apéry basis element. -/
def TerminalApery (m a b c n : ℕ) : Prop :=
  n ∈ generatedApery m a b c ∧
    n+a ∉ generatedApery m a b c ∧
    n+b ∉ generatedApery m a b c ∧
    n+c ∉ generatedApery m a b c

theorem pseudoFrobenius_add_m_terminal (m a b c f : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hf : IsPseudoFrobenius m a b c f) :
    TerminalApery m a b c (f+m) := by
  have hg := generatedSemigroup_generators m a b c
  have hstep : ∀ g ∈ generatedSemigroup m a b c, 0 < g →
      f+m+g ∉ generatedApery m a b c := by
    intro g hgs hgp hn
    have hmem : f+m+g-m ∈ generatedSemigroup m a b c := by
      have he : f+m+g-m = f+g := by omega
      rw [he]
      exact hf.2 g hgs hgp
    rcases hn.2 with hsmall | hnot
    · omega
    · exact hnot hmem
  refine ⟨⟨hf.2 m hg.1 hm, Or.inr ?_⟩,
    hstep a hg.2.1 ha, hstep b hg.2.2.1 hb, hstep c hg.2.2.2 hc⟩
  simpa using hf.1

/-- Conversely, a terminal Apéry element above m gives an actual PF gap. -/
theorem terminal_sub_m_pseudoFrobenius (m a b c n : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hge : m ≤ n) (hn : TerminalApery m a b c n) :
    IsPseudoFrobenius m a b c (n-m) := by
  apply (isPseudoFrobenius_iff_generators m a b c (n-m) hm ha hb hc).mpr
  have hg := generatedSemigroup_generators m a b c
  have hgap : n-m ∉ generatedSemigroup m a b c := by
    rcases hn.1.2 with hsmall | hnot
    · omega
    · exact hnot
  have hstep : ∀ g ∈ generatedSemigroup m a b c,
      n+g ∉ generatedApery m a b c →
      n-m+g ∈ generatedSemigroup m a b c := by
    intro g hg hnot
    have hsum := generatedSemigroup_add m a b c hn.1.1 hg
    have hpred : n+g-m ∈ generatedSemigroup m a b c := by
      by_contra habs
      exact hnot ⟨hsum, Or.inr habs⟩
    have he : n+g-m = n-m+g := by omega
    rwa [he] at hpred
  refine ⟨hgap, ?_, hstep a hg.2.1 hn.2.1,
    hstep b hg.2.2.1 hn.2.2.1, hstep c hg.2.2.2 hn.2.2.2⟩
  simpa [Nat.sub_add_cancel hge] using hn.1.1

/-- Coordinatewise maximal elements of the actual finite set D. -/
noncomputable def maximalPoints (D : Finset Point3) : Finset Point3 := by
  classical
  exact D.filter (fun p => ∀ q ∈ D, p ≤ q → q = p)

theorem mem_maximalPoints (D : Finset Point3) (p : Point3) :
    p ∈ maximalPoints D ↔ p ∈ D ∧ ∀ q ∈ D, p ≤ q → q = p := by
  classical
  simp [maximalPoints]

/-- The PF-to-corner step uses the real canonical Apéry set and down-closure. -/
theorem terminal_canonical_maximal (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    {p : Point3} (hp : p ∈ aperyStandardSet m a b c hm hgcd)
    (ht : TerminalApery m a b c (aperyWeight a b c p)) :
    p ∈ maximalPoints (aperyStandardSet m a b c hm hgcd) := by
  classical
  let D := aperyStandardSet m a b c hm hgcd
  have hd : IsDownset D := aperyStandardSet_downset m a b c hm hgcd
  have h1 : p+Point3.e1 ∉ D := by
    intro h
    apply ht.2.1
    have hAp := canonical_weight_mem_generatedApery m a b c hm
      ((mem_aperyStandardSet m a b c hm hgcd _).mp h)
    convert hAp using 1 <;> simp [aperyWeight, Point3.e1] <;> ring
  have h2 : p+Point3.e2 ∉ D := by
    intro h
    apply ht.2.2.1
    have hAp := canonical_weight_mem_generatedApery m a b c hm
      ((mem_aperyStandardSet m a b c hm hgcd _).mp h)
    convert hAp using 1 <;> simp [aperyWeight, Point3.e2] <;> ring
  have h3 : p+Point3.e3 ∉ D := by
    intro h
    apply ht.2.2.2
    have hAp := canonical_weight_mem_generatedApery m a b c hm
      ((mem_aperyStandardSet m a b c hm hgcd _).mp h)
    convert hAp using 1 <;> simp [aperyWeight, Point3.e3] <;> ring
  apply (mem_maximalPoints _ _).mpr
  refine ⟨hp, ?_⟩
  intro q hq hpq
  rcases hpq with ⟨hpx,hpy,hpz⟩
  have hqx : q.x ≤ p.x := by
    by_contra h
    apply h1
    apply hd (b := q) ?_ hq
    change p.x+1 ≤ q.x ∧ p.y+0 ≤ q.y ∧ p.z+0 ≤ q.z
    exact ⟨by omega, by omega, by omega⟩
  have hqy : q.y ≤ p.y := by
    by_contra h
    apply h2
    apply hd (b := q) ?_ hq
    change p.x+0 ≤ q.x ∧ p.y+1 ≤ q.y ∧ p.z+0 ≤ q.z
    exact ⟨by omega, by omega, by omega⟩
  have hqz : q.z ≤ p.z := by
    by_contra h
    apply h3
    apply hd (b := q) ?_ hq
    change p.x+0 ≤ q.x ∧ p.y+0 ≤ q.y ∧ p.z+1 ≤ q.z
    exact ⟨by omega, by omega, by omega⟩
  apply Point3.ext <;> omega

/-- Every genuine PF gap is represented by a maximal canonical point. -/
theorem pseudoFrobenius_has_maximal_representative (m a b c f : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1)
    (hf : IsPseudoFrobenius m a b c f) :
    ∃ p ∈ maximalPoints (aperyStandardSet m a b c hm hgcd),
      f = aperyWeight a b c p-m := by
  have ht := pseudoFrobenius_add_m_terminal m a b c f hm ha hb hc hf
  have hAp := ht.1
  rw [generatedApery_eq_weights m a b c hm hgcd] at hAp
  obtain ⟨p,hp,he⟩ := hAp
  refine ⟨p, terminal_canonical_maximal m a b c hm hgcd hp ?_, ?_⟩
  · rwa [← he]
  · omega

/-- A finite collection defined by actual PF membership; membership is proved below. -/
noncomputable def pseudoFrobeniusFinset (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) : Finset ℕ := by
  classical
  exact ((maximalPoints (aperyStandardSet m a b c hm hgcd)).image
    (fun p => aperyWeight a b c p-m)).filter (IsPseudoFrobenius m a b c)

theorem mem_pseudoFrobeniusFinset (m a b c f : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    f ∈ pseudoFrobeniusFinset m a b c hm hgcd ↔
      IsPseudoFrobenius m a b c f := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    obtain ⟨p,hp,he⟩ :=
      pseudoFrobenius_has_maximal_representative m a b c f hm ha hb hc hgcd h
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨p,hp,he.symm⟩, h⟩

/-- Unconditional counting inequality for the actual nonnegative PF gaps. -/
theorem pseudoFrobenius_card_le_maximalPoints (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c)) = 1) :
    (pseudoFrobeniusFinset m a b c hm hgcd).card ≤
      (maximalPoints (aperyStandardSet m a b c hm hgcd)).card := by
  classical
  exact (Finset.card_filter_le _ _).trans (Finset.card_image_le)

end NSP3.V03
