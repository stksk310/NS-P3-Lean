import NSP3.V03.BettiApery
import NSP3.SharpnessApery

/-! Exact maximal-point counts of the existing, actual even and odd Apéry regions. -/

namespace NSP3.V03

open NSP3.Sharpness

def RegionMaximal (P : Point3 → Prop) (p : Point3) : Prop :=
  P p ∧ ∀ q, P q → p ≤ q → q = p

private theorem regionMaximal_iff_steps (P : Point3 → Prop)
    (hd : ∀ {p q}, p ≤ q → P q → P p) (p : Point3) :
    RegionMaximal P p ↔ P p ∧
      ¬ P (p+Point3.e1) ∧ ¬ P (p+Point3.e2) ∧ ¬ P (p+Point3.e3) := by
  constructor
  · rintro ⟨hp,hmax⟩
    refine ⟨hp, ?_, ?_, ?_⟩
    · intro h
      have he := hmax (p+Point3.e1) h
        (show p ≤ p+Point3.e1 from ⟨by simp, by simp, by simp⟩)
      have hx := congrArg Point3.x he
      simp only [Point3.add_x,Point3.e1_x] at hx
      omega
    · intro h
      have he := hmax (p+Point3.e2) h
        (show p ≤ p+Point3.e2 from ⟨by simp, by simp, by simp⟩)
      have hy := congrArg Point3.y he
      simp only [Point3.add_y,Point3.e2_y] at hy
      omega
    · intro h
      have he := hmax (p+Point3.e3) h
        (show p ≤ p+Point3.e3 from ⟨by simp, by simp, by simp⟩)
      have hz := congrArg Point3.z he
      simp only [Point3.add_z,Point3.e3_z] at hz
      omega
  · rintro ⟨hp,h1,h2,h3⟩
    refine ⟨hp, ?_⟩
    intro q hq hpq
    rcases hpq with ⟨hx,hy,hz⟩
    have qx : q.x ≤ p.x := by
      by_contra h
      apply h1
      apply hd (q := q) ?_ hq
      change p.x+1 ≤ q.x ∧ p.y+0 ≤ q.y ∧ p.z+0 ≤ q.z
      exact ⟨by omega,by omega,by omega⟩
    have qy : q.y ≤ p.y := by
      by_contra h
      apply h2
      apply hd (q := q) ?_ hq
      change p.x+0 ≤ q.x ∧ p.y+1 ≤ q.y ∧ p.z+0 ≤ q.z
      exact ⟨by omega,by omega,by omega⟩
    have qz : q.z ≤ p.z := by
      by_contra h
      apply h3
      apply hd (q := q) ?_ hq
      change p.x+0 ≤ q.x ∧ p.y+0 ≤ q.y ∧ p.z+1 ≤ q.z
      exact ⟨by omega,by omega,by omega⟩
    apply Point3.ext <;> omega

private theorem evenRegion_downward (L k : ℕ) {p q : Point3}
    (hpq : p ≤ q) (hq : EvenRegion L k q) : EvenRegion L k p := by
  rcases hpq with ⟨hx,hy,hz⟩
  rcases hq with h | h | h
  · exact Or.inl ⟨by omega,by omega⟩
  · exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  · exact Or.inr (Or.inr ⟨by omega,by omega,by omega⟩)

private theorem oddRegion_downward (L k : ℕ) {p q : Point3}
    (hpq : p ≤ q) (hq : OddRegion L k q) : OddRegion L k p := by
  rcases hpq with ⟨hx,hy,hz⟩
  rcases hq with h | h | h
  · exact Or.inl ⟨by omega,by omega⟩
  · exact Or.inr (Or.inl ⟨by omega,by omega⟩)
  · exact Or.inr (Or.inr ⟨by omega,by omega,by omega⟩)

private def maxLeft (k : ℕ) : Finset Point3 :=
  (Finset.range k).image (fun j => ⟨j,k-j,0⟩)

private def maxRight (k : ℕ) : Finset Point3 :=
  (Finset.Icc 1 k).image (fun j => ⟨0,k-j,j⟩)

def evenMaxima (L k : ℕ) : Finset Point3 :=
  insert ⟨L-1,0,0⟩ (maxLeft k ∪ maxRight k)

def oddMaxima (L k : ℕ) : Finset Point3 :=
  insert ⟨L,0,0⟩ (maxLeft k ∪ maxRight (k-1))

private theorem mem_maxLeft (k : ℕ) (p : Point3) :
    p ∈ maxLeft k ↔ p.z=0 ∧ 0<p.y ∧ p.x+p.y=k := by
  simp only [maxLeft,Finset.mem_image,Finset.mem_range]
  constructor
  · rintro ⟨j,hj,rfl⟩
    dsimp
    omega
  · rintro ⟨hz,hy,hxy⟩
    refine ⟨p.x,by omega,?_⟩
    apply Point3.ext <;> dsimp <;> omega

private theorem mem_maxRight (k : ℕ) (p : Point3) :
    p ∈ maxRight k ↔ p.x=0 ∧ 0<p.z ∧ p.y+p.z=k := by
  simp only [maxRight,Finset.mem_image,Finset.mem_Icc]
  constructor
  · rintro ⟨j,⟨hj,hj'⟩,rfl⟩
    dsimp
    omega
  · rintro ⟨hx,hz,hyz⟩
    refine ⟨p.z,⟨by omega,by omega⟩,?_⟩
    apply Point3.ext <;> dsimp <;> omega

theorem evenRegion_maximal_iff (L k : ℕ) (hk : 1 ≤ k) (hL : k<L) (p : Point3) :
    RegionMaximal (EvenRegion L k) p ↔ p ∈ evenMaxima L k := by
  rw [regionMaximal_iff_steps _ (evenRegion_downward L k)]
  simp only [evenMaxima,Finset.mem_insert,Finset.mem_union,mem_maxLeft,mem_maxRight]
  constructor
  · rintro ⟨hp,h1,h2,h3⟩
    by_cases hz : p.z=0
    · by_cases hy : p.y=0
      · left
        have hx : p.x<L := by rcases hp with h | h | h <;> omega
        have hx' : ¬p.x+1<L := by
          intro h
          apply h1
          simp [EvenRegion,hy,hz,Point3.e1,h]
        apply Point3.ext <;> dsimp <;> omega
      · right; left
        refine ⟨hz,by omega,?_⟩
        have hs : p.x+p.y≤k := by rcases hp with h | h | h <;> omega
        by_contra hne
        have hs' : p.x+(p.y+1)≤k := by omega
        apply h2
        exact Or.inl ⟨by simpa [Point3.e2] using hz,by simpa [Point3.e2] using hs'⟩
    · right; right
      have hx : p.x=0 := by rcases hp with h | h | h <;> omega
      have hs : p.y+p.z≤k := by rcases hp with h | h | h <;> omega
      refine ⟨hx,by omega,?_⟩
      by_contra hne
      have hs' : p.y+(p.z+1)≤k := by omega
      apply h3
      exact Or.inr (Or.inl ⟨by simpa [Point3.e3] using hx,
        by simpa [Point3.e3] using hs'⟩)
  · rintro (rfl | h | h)
    · refine ⟨Or.inr (Or.inr ⟨rfl,rfl,by dsimp; omega⟩),?_,?_,?_⟩
      all_goals
        intro h
        rcases h with h | h | h <;>
          simp only [Point3.add_x,Point3.add_y,Point3.add_z,
            Point3.e1_x,Point3.e1_y,Point3.e1_z,Point3.e2_x,Point3.e2_y,Point3.e2_z,
            Point3.e3_x,Point3.e3_y,Point3.e3_z] at h <;> omega
    · obtain ⟨hz,hy,hs⟩ := h
      simp only [EvenRegion,Point3.add_x,Point3.add_y,Point3.add_z,
        Point3.e1_x,Point3.e1_y,Point3.e1_z,Point3.e2_x,Point3.e2_y,Point3.e2_z,
        Point3.e3_x,Point3.e3_y,Point3.e3_z]
      omega
    · obtain ⟨hx,hz,hs⟩ := h
      simp only [EvenRegion,Point3.add_x,Point3.add_y,Point3.add_z,
        Point3.e1_x,Point3.e1_y,Point3.e1_z,Point3.e2_x,Point3.e2_y,Point3.e2_z,
        Point3.e3_x,Point3.e3_y,Point3.e3_z]
      omega

theorem oddRegion_maximal_iff (L k : ℕ) (hk : 2 ≤ k) (hL : k≤L) (p : Point3) :
    RegionMaximal (OddRegion L k) p ↔ p ∈ oddMaxima L k := by
  rw [regionMaximal_iff_steps _ (oddRegion_downward L k)]
  simp only [oddMaxima,Finset.mem_insert,Finset.mem_union,mem_maxLeft,mem_maxRight]
  constructor
  · rintro ⟨hp,h1,h2,h3⟩
    by_cases hz : p.z=0
    · by_cases hy : p.y=0
      · left
        have hx : p.x≤L := by rcases hp with h | h | h <;> omega
        have hx' : ¬p.x+1≤L := by
          intro h
          apply h1
          simp [OddRegion,hy,hz,Point3.e1,h]
        apply Point3.ext <;> dsimp <;> omega
      · right; left
        refine ⟨hz,by omega,?_⟩
        have hs : p.x+p.y≤k := by rcases hp with h | h | h <;> omega
        by_contra hne
        have hs' : p.x+(p.y+1)≤k := by omega
        apply h2
        exact Or.inl ⟨by simpa [Point3.e2] using hz,by simpa [Point3.e2] using hs'⟩
    · right; right
      have hx : p.x=0 := by rcases hp with h | h | h <;> omega
      have hs : p.y+p.z<k := by rcases hp with h | h | h <;> omega
      refine ⟨hx,by omega,?_⟩
      by_contra hne
      have hs' : p.y+(p.z+1)<k := by omega
      apply h3
      exact Or.inr (Or.inl ⟨by simpa [Point3.e3] using hx,
        by simpa [Point3.e3] using hs'⟩)
  · rintro (rfl | h | h)
    · refine ⟨Or.inr (Or.inr ⟨rfl,rfl,by dsimp; omega⟩),?_,?_,?_⟩
      all_goals
        intro h
        rcases h with h | h | h <;>
          simp only [Point3.add_x,Point3.add_y,Point3.add_z,
            Point3.e1_x,Point3.e1_y,Point3.e1_z,Point3.e2_x,Point3.e2_y,Point3.e2_z,
            Point3.e3_x,Point3.e3_y,Point3.e3_z] at h <;> omega
    · obtain ⟨hz,hy,hs⟩ := h
      simp only [OddRegion,Point3.add_x,Point3.add_y,Point3.add_z,
        Point3.e1_x,Point3.e1_y,Point3.e1_z,Point3.e2_x,Point3.e2_y,Point3.e2_z,
        Point3.e3_x,Point3.e3_y,Point3.e3_z]
      omega
    · obtain ⟨hx,hz,hs⟩ := h
      simp only [OddRegion,Point3.add_x,Point3.add_y,Point3.add_z,
        Point3.e1_x,Point3.e1_y,Point3.e1_z,Point3.e2_x,Point3.e2_y,Point3.e2_z,
        Point3.e3_x,Point3.e3_y,Point3.e3_z]
      omega

private theorem maxLeft_card (k : ℕ) : (maxLeft k).card=k := by
  unfold maxLeft
  rw [Finset.card_image_iff.mpr ?_,Finset.card_range]
  intro i _ j _ h
  exact congrArg Point3.x h

private theorem maxRight_card (k : ℕ) : (maxRight k).card=k := by
  unfold maxRight
  rw [Finset.card_image_iff.mpr ?_]
  · simp
  · intro i _ j _ h
    exact congrArg Point3.z h

theorem evenMaxima_card (L k : ℕ) : (evenMaxima L k).card=2*k+1 := by
  have hd : Disjoint (maxLeft k) (maxRight k) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rw [mem_maxLeft] at hp
    rw [mem_maxRight] at hq
    omega
  have hn : (⟨L-1,0,0⟩ : Point3) ∉ maxLeft k ∪ maxRight k := by
    simp [mem_maxLeft,mem_maxRight]
  unfold evenMaxima
  rw [Finset.card_insert_of_notMem hn,Finset.card_union_of_disjoint hd,
    maxLeft_card,maxRight_card]
  omega

theorem oddMaxima_card (L k : ℕ) (hk : 1≤k) : (oddMaxima L k).card=2*k := by
  have hd : Disjoint (maxLeft k) (maxRight (k-1)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    rw [mem_maxLeft] at hp
    rw [mem_maxRight] at hq
    omega
  have hn : (⟨L,0,0⟩ : Point3) ∉ maxLeft k ∪ maxRight (k-1) := by
    simp [mem_maxLeft,mem_maxRight]
  unfold oddMaxima
  rw [Finset.card_insert_of_notMem hn,Finset.card_union_of_disjoint hd,
    maxLeft_card,maxRight_card]
  omega

/-- Specialization to the existing canonical set, not a replacement region predicate. -/
theorem canonical_even_maximalPoints (m k L a b c : ℕ) (hk : 1≤k)
    (hL : k<L) (hm : L+k*k+k=m)
    (ha : a+1=(k+1)*m) (hb : b=L*m+k) (hc : c=b+1)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    maximalPoints (aperyStandardSet m a b c (by nlinarith) hgcd) = evenMaxima L k := by
  classical
  have hpos : 0 < m := by nlinarith
  have hmem : ∀ p, p ∈ aperyStandardSet m a b c hpos hgcd ↔ EvenRegion L k p := by
    intro p
    exact (mem_aperyStandardSet m a b c hpos hgcd p).trans
      (even_canonical_iff m k L a b c (by omega) hL hm ha hb hc hgcd p)
  ext p
  rw [mem_maximalPoints,← evenRegion_maximal_iff L k hk hL]
  constructor
  · rintro ⟨hp,hmax⟩
    exact ⟨(hmem p).mp hp,fun q hq hpq => hmax q ((hmem q).mpr hq) hpq⟩
  · rintro ⟨hp,hmax⟩
    exact ⟨(hmem p).mpr hp,fun q hq hpq => hmax q ((hmem q).mp hq) hpq⟩

theorem canonical_odd_maximalPoints (m k L a b c : ℕ) (hk : 2≤k)
    (hL : k≤L) (hm : L+k*k+1=m)
    (ha : a+1=k*m) (hb : b=L*m+k) (hc : c=b+1)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) :
    maximalPoints (aperyStandardSet m a b c (by nlinarith) hgcd) = oddMaxima L k := by
  classical
  have hpos : 0 < m := by nlinarith
  have hmem : ∀ p, p ∈ aperyStandardSet m a b c hpos hgcd ↔ OddRegion L k p := by
    intro p
    exact (mem_aperyStandardSet m a b c hpos hgcd p).trans
      (odd_canonical_iff m k L a b c hk hL hm ha hb hc hgcd p)
  ext p
  rw [mem_maximalPoints,← oddRegion_maximal_iff L k hk hL]
  constructor
  · rintro ⟨hp,hmax⟩
    exact ⟨(hmem p).mp hp,fun q hq hpq => hmax q ((hmem q).mpr hq) hpq⟩
  · rintro ⟨hp,hmax⟩
    exact ⟨(hmem p).mpr hp,fun q hq hpq => hmax q ((hmem q).mp hq) hpq⟩

end NSP3.V03
