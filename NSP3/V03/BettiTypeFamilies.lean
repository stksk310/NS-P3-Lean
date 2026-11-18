import NSP3.V03.BettiFamilies

/-!
Actual pseudo-Frobenius counts for the published even and odd families.
This file does not define a Betti sequence by a formula and call it a Tor rank.
-/

namespace NSP3.V03

open NSP3.Sharpness

theorem maximal_weight_terminal_of_unique (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1)
    (hunique : ∀ p ∈ aperyStandardSet m a b c hm hgcd, ∀ q : Point3,
      aperyWeight a b c p = aperyWeight a b c q → q=p)
    {p : Point3} (hp : p ∈ maximalPoints (aperyStandardSet m a b c hm hgcd)) :
    TerminalApery m a b c (aperyWeight a b c p) := by
  classical
  obtain ⟨hpm,hmax⟩ := (mem_maximalPoints _ _).mp hp
  have hstep (u : Point3) (g : ℕ)
      (hw : aperyWeight a b c u = aperyWeight a b c p+g)
      (hpu : p≤u) (hne : u≠p) :
      aperyWeight a b c p+g ∉ generatedApery m a b c := by
    intro hAp
    rw [generatedApery_eq_weights m a b c hm hgcd] at hAp
    obtain ⟨q,hq,he⟩ := hAp
    have hwu : aperyWeight a b c q = aperyWeight a b c u := by omega
    have huq := hunique q hq u hwu
    have hu : u ∈ aperyStandardSet m a b c hm hgcd := by rw [huq]; exact hq
    exact hne (hmax u hu hpu)
  refine ⟨canonical_weight_mem_generatedApery m a b c hm
    ((mem_aperyStandardSet m a b c hm hgcd _).mp hpm), ?_, ?_, ?_⟩
  · apply hstep (p+Point3.e1) a
    · simp [aperyWeight,Point3.e1]; ring
    · change p.x≤p.x+1 ∧ p.y≤p.y+0 ∧ p.z≤p.z+0
      exact ⟨by omega,by omega,by omega⟩
    · intro he
      have hx := congrArg Point3.x he
      simp only [Point3.add_x,Point3.e1_x] at hx
      omega
  · apply hstep (p+Point3.e2) b
    · simp [aperyWeight,Point3.e2]; ring
    · change p.x≤p.x+0 ∧ p.y≤p.y+1 ∧ p.z≤p.z+0
      exact ⟨by omega,by omega,by omega⟩
    · intro he
      have hy := congrArg Point3.y he
      simp only [Point3.add_y,Point3.e2_y] at hy
      omega
  · apply hstep (p+Point3.e3) c
    · simp [aperyWeight,Point3.e3]; ring
    · change p.x≤p.x+0 ∧ p.y≤p.y+0 ∧ p.z≤p.z+1
      exact ⟨by omega,by omega,by omega⟩
    · intro he
      have hz := congrArg Point3.z he
      simp only [Point3.add_z,Point3.e3_z] at hz
      omega

theorem maximal_weight_ge_m (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1)
    (hma : m≤a) (hmb : m≤b) (hmc : m≤c)
    (he1 : Point3.e1 ∈ aperyStandardSet m a b c hm hgcd)
    {p : Point3} (hp : p ∈ maximalPoints (aperyStandardSet m a b c hm hgcd)) :
    m≤aperyWeight a b c p := by
  obtain ⟨_,hmax⟩ := (mem_maximalPoints _ _).mp hp
  by_contra h
  have hx : p.x=0 := by
    by_contra hne
    have hpos : 1≤p.x := by omega
    have ha : a≤a*p.x := by simpa using Nat.mul_le_mul_left a hpos
    have hw : m≤aperyWeight a b c p := by unfold aperyWeight; omega
    exact h hw
  have hy : p.y=0 := by
    by_contra hne
    have hpos : 1≤p.y := by omega
    have hb : b≤b*p.y := by simpa using Nat.mul_le_mul_left b hpos
    have hw : m≤aperyWeight a b c p := by unfold aperyWeight; omega
    exact h hw
  have hz : p.z=0 := by
    by_contra hne
    have hpos : 1≤p.z := by omega
    have hc : c≤c*p.z := by simpa using Nat.mul_le_mul_left c hpos
    have hw : m≤aperyWeight a b c p := by unfold aperyWeight; omega
    exact h hw
  have hle : p≤Point3.e1 := by
    change p.x≤1 ∧ p.y≤0 ∧ p.z≤0
    exact ⟨by omega,by omega,by omega⟩
  have he := congrArg Point3.x (hmax Point3.e1 he1 hle)
  simp only [Point3.e1_x] at he
  omega

theorem pseudoFrobenius_card_eq_maximalPoints_of_unique (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1)
    (hma : m≤a) (hmb : m≤b) (hmc : m≤c)
    (he1 : Point3.e1 ∈ aperyStandardSet m a b c hm hgcd)
    (hunique : ∀ p ∈ aperyStandardSet m a b c hm hgcd, ∀ q : Point3,
      aperyWeight a b c p = aperyWeight a b c q → q=p) :
    (pseudoFrobeniusFinset m a b c hm hgcd).card =
      (maximalPoints (aperyStandardSet m a b c hm hgcd)).card := by
  classical
  let D := maximalPoints (aperyStandardSet m a b c hm hgcd)
  have hpf : ∀ p∈D, IsPseudoFrobenius m a b c (aperyWeight a b c p-m) := by
    intro p hp
    exact terminal_sub_m_pseudoFrobenius m a b c _ hm (by omega) (by omega) (by omega)
      (maximal_weight_ge_m m a b c hm hgcd hma hmb hmc he1 hp)
      (maximal_weight_terminal_of_unique m a b c hm hgcd hunique hp)
  have hfilter : (D.image (fun p => aperyWeight a b c p-m)).filter
      (IsPseudoFrobenius m a b c) = D.image (fun p => aperyWeight a b c p-m) := by
    apply Finset.filter_eq_self.mpr
    intro f hf
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hf
    exact hpf p hp
  change ((D.image (fun p => aperyWeight a b c p-m)).filter
    (IsPseudoFrobenius m a b c)).card = D.card
  rw [hfilter]
  apply Finset.card_image_iff.mpr
  intro p hp q hq he
  have hwp := maximal_weight_ge_m m a b c hm hgcd hma hmb hmc he1 hp
  have hwq := maximal_weight_ge_m m a b c hm hgcd hma hmb hmc he1 hq
  change aperyWeight a b c p-m = aperyWeight a b c q-m at he
  have hw : aperyWeight a b c p = aperyWeight a b c q := by omega
  have hpm := ((mem_maximalPoints _ _).mp hp).1
  exact (hunique p hpm q hw).symm

/-- Actual PF cardinality for the even numeric construction, for every parameter. -/
theorem even_family_pseudoFrobenius_card (m k L a b c : ℕ) (hk : 1≤k)
    (hL : k<L) (hm : L+k*k+k=m)
    (ha : a+1=(k+1)*m) (hb : b=L*m+k) (hc : c=b+1)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    (pseudoFrobeniusFinset m a b c (by nlinarith) hgcd).card=2*k+1 := by
  have hpos : 0 < m := by nlinarith
  have hma : m≤a := by nlinarith [Nat.mul_le_mul_right m hk]
  have hmb : m≤b := by
    nlinarith [Nat.mul_le_mul_right m (show 1≤L by omega)]
  have hmc : m≤c := by omega
  have hregion : ∀ p, p∈aperyStandardSet m a b c hpos hgcd ↔ EvenRegion L k p := by
    intro p
    exact (mem_aperyStandardSet m a b c hpos hgcd p).trans
      (even_canonical_iff m k L a b c (by omega) hL hm ha hb hc hgcd p)
  have he1 : Point3.e1 ∈ aperyStandardSet m a b c hpos hgcd := by
    apply (hregion _).mpr
    exact Or.inl ⟨rfl,by simpa [Point3.e1] using hk⟩
  have hu : ∀ p∈aperyStandardSet m a b c hpos hgcd, ∀ q : Point3,
      aperyWeight a b c p = aperyWeight a b c q → q=p := by
    intro p hp q he
    exact (even_unique_factorization m k L a b c (by omega) hL hm ha hb hc hgcd
      ((hregion p).mp hp) 0 (by simpa using he)).2
  rw [pseudoFrobenius_card_eq_maximalPoints_of_unique m a b c hpos hgcd hma hmb hmc he1 hu,
    canonical_even_maximalPoints m k L a b c hk hL hm ha hb hc hgcd]
  exact evenMaxima_card L k

/-- Actual PF cardinality for the odd numeric construction, for every parameter. -/
theorem odd_family_pseudoFrobenius_card (m k L a b c : ℕ) (hk : 2≤k)
    (hL : k≤L) (hm : L+k*k+1=m)
    (ha : a+1=k*m) (hb : b=L*m+k) (hc : c=b+1)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    (pseudoFrobeniusFinset m a b c (by nlinarith) hgcd).card=2*k := by
  have hpos : 0 < m := by nlinarith
  have hma : m≤a := by nlinarith [Nat.mul_le_mul_right m hk]
  have hmb : m≤b := by
    nlinarith [Nat.mul_le_mul_right m (show 1≤L by omega)]
  have hmc : m≤c := by omega
  have hregion : ∀ p, p∈aperyStandardSet m a b c hpos hgcd ↔ OddRegion L k p := by
    intro p
    exact (mem_aperyStandardSet m a b c hpos hgcd p).trans
      (odd_canonical_iff m k L a b c hk hL hm ha hb hc hgcd p)
  have he1 : Point3.e1 ∈ aperyStandardSet m a b c hpos hgcd := by
    apply (hregion _).mpr
    exact Or.inl ⟨rfl,by simp [Point3.e1]; omega⟩
  have hu : ∀ p∈aperyStandardSet m a b c hpos hgcd, ∀ q : Point3,
      aperyWeight a b c p = aperyWeight a b c q → q=p := by
    intro p hp q he
    exact (odd_unique_factorization m k L a b c hk hL hm ha hb hc hgcd
      ((hregion p).mp hp) 0 (by simpa using he)).2
  rw [pseudoFrobenius_card_eq_maximalPoints_of_unique m a b c hpos hgcd hma hmb hmc he1 hu,
    canonical_odd_maximalPoints m k L a b c hk hL hm ha hb hc hgcd]
  exact oddMaxima_card L k (by omega)

end NSP3.V03
