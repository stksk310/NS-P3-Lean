import NSP3.GeneratedSemigroupApery

namespace NSP3.Sharpness

/-- The two triangular faces and the long first-coordinate arm. -/
def EvenRegion (L k : ℕ) (p : Point3) : Prop :=
  (p.z = 0 ∧ p.x+p.y ≤ k) ∨
  (p.x = 0 ∧ p.y+p.z ≤ k) ∨
  (p.y = 0 ∧ p.z = 0 ∧ p.x < L)

def evenIndex (k : ℕ) (p : Point3) : ℤ :=
  -(p.x : ℤ)+(k : ℤ)*p.y+((k : ℤ)+1)*p.z

private theorem bounded_dvd_zero {n d : ℤ} (hn : 0 < n)
    (hl : -n < d) (hu : d < n) (hd : n ∣ d) : d = 0 := by
  obtain ⟨t,rfl⟩ := hd
  by_cases ht : t = 0
  · simp [ht]
  · by_cases hp : 0 < t
    · have : 1 ≤ t := by omega
      nlinarith
    · have : t ≤ -1 := by omega
      nlinarith

private theorem left_left (k x y u v : ℤ)
    (hk : 0 < k) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hxy : x+y ≤ k) (huv : u+v ≤ k)
    (he : -x+k*y = -u+k*v) : x=u ∧ y=v := by
  have hd : k+1 ∣ (x+y)-(u+v) := by
    use (y-v)
    nlinarith
  have hz := bounded_dvd_zero (by omega : 0 < k+1)
    (by omega : -(k+1) < (x+y)-(u+v))
    (by omega : (x+y)-(u+v) < k+1) hd
  constructor <;> nlinarith

private theorem right_right (k y z v w : ℤ)
    (hk : 0 < k) (hy : 0 ≤ y) (hz : 0 ≤ z) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hyz : y+z ≤ k) (hvw : v+w ≤ k)
    (he : k*y+(k+1)*z = k*v+(k+1)*w) : y=v ∧ z=w := by
  have hd : k+1 ∣ y-v := by
    use (y+z)-(v+w)
    nlinarith
  have heq := bounded_dvd_zero (by omega : 0 < k+1)
    (by omega : -(k+1) < y-v) (by omega : y-v < k+1) hd
  constructor <;> nlinarith

private theorem left_right (k x y v w : ℤ)
    (hk : 0 < k) (hx : 0 ≤ x) (_hy : 0 ≤ y) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hxy : x+y ≤ k) (_hvw : v+w ≤ k)
    (he : -x+k*y = k*v+(k+1)*w) : x=0 ∧ y=v ∧ w=0 := by
  have hsmall : x+w < k := by
    by_contra h
    have : k ≤ x+w := by omega
    nlinarith [mul_nonneg hk.le hx, mul_nonneg hk.le hv]
  have heq : k*(y-v-w)=x+w := by nlinarith
  have hzero : x+w=0 := by
    by_cases h : y-v-w ≤ 0
    · nlinarith
    · have : 1 ≤ y-v-w := by omega
      nlinarith
  have hx0 : x=0 := by omega
  have hw0 : w=0 := by omega
  refine ⟨hx0,?_,hw0⟩
  nlinarith

/-- A symbolic uniqueness result, with no finite parameter checking. -/
theorem evenIndex_injective (L k : ℕ) (hk : 0 < k) {p q : Point3}
    (hp : EvenRegion L k p) (hq : EvenRegion L k q)
    (he : evenIndex k p = evenIndex k q) : p=q := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have px : (0 : ℤ) ≤ p.x := by omega
  have py : (0 : ℤ) ≤ p.y := by omega
  have pz : (0 : ℤ) ≤ p.z := by omega
  have qx : (0 : ℤ) ≤ q.x := by omega
  have qy : (0 : ℤ) ≤ q.y := by omega
  have qz : (0 : ℤ) ≤ q.z := by omega
  unfold evenIndex at he
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq
  · obtain ⟨pz0,hpb⟩ := hp; obtain ⟨qz0,hqb⟩ := hq
    have hpb' : (p.x : ℤ)+p.y ≤ k := by exact_mod_cast hpb
    have hqb' : (q.x : ℤ)+q.y ≤ k := by exact_mod_cast hqb
    simp only [pz0,qz0,Nat.cast_zero,mul_zero,add_zero] at he
    obtain ⟨hx,hy⟩ := left_left k p.x p.y q.x q.y hk' px py qx qy hpb' hqb' he
    apply Point3.ext <;> omega
  · obtain ⟨pz0,hpb⟩ := hp; obtain ⟨qx0,hqb⟩ := hq
    have hpb' : (p.x : ℤ)+p.y ≤ k := by exact_mod_cast hpb
    have hqb' : (q.y : ℤ)+q.z ≤ k := by exact_mod_cast hqb
    simp only [pz0,qx0,Nat.cast_zero,mul_zero,add_zero,neg_zero,zero_add] at he
    obtain ⟨hx,hy,hz⟩ := left_right k p.x p.y q.y q.z hk' px py qy qz hpb' hqb' he
    apply Point3.ext <;> omega
  · obtain ⟨pz0,hpb⟩ := hp; obtain ⟨qy0,qz0,_⟩ := hq
    have hpb' : (p.x : ℤ)+p.y ≤ k := by exact_mod_cast hpb
    simp only [pz0,qy0,qz0,Nat.cast_zero,mul_zero,add_zero] at he
    have hy0 : p.y=0 := by
      by_contra h
      have : (1 : ℤ) ≤ p.y := by omega
      nlinarith
    apply Point3.ext <;> simp_all
  · obtain ⟨px0,hpb⟩ := hp; obtain ⟨qz0,hqb⟩ := hq
    have hpb' : (p.y : ℤ)+p.z ≤ k := by exact_mod_cast hpb
    have hqb' : (q.x : ℤ)+q.y ≤ k := by exact_mod_cast hqb
    simp only [px0,qz0,Nat.cast_zero,mul_zero,add_zero,neg_zero,zero_add] at he
    obtain ⟨hx,hy,hz⟩ := left_right k q.x q.y p.y p.z hk' qx qy py pz hqb' hpb' he.symm
    apply Point3.ext <;> omega
  · obtain ⟨px0,hpb⟩ := hp; obtain ⟨qx0,hqb⟩ := hq
    have hpb' : (p.y : ℤ)+p.z ≤ k := by exact_mod_cast hpb
    have hqb' : (q.y : ℤ)+q.z ≤ k := by exact_mod_cast hqb
    simp only [px0,qx0,Nat.cast_zero,neg_zero,zero_add] at he
    obtain ⟨hy,hz⟩ := right_right k p.y p.z q.y q.z hk' py pz qy qz hpb' hqb' he
    apply Point3.ext <;> omega
  · obtain ⟨px0,_⟩ := hp; obtain ⟨qy0,qz0,_⟩ := hq
    simp only [px0,qy0,qz0,Nat.cast_zero,neg_zero,zero_add,mul_zero,add_zero] at he
    have : (p.y : ℤ)=0 ∧ (p.z : ℤ)=0 ∧ (q.x : ℤ)=0 := by
      constructor
      · nlinarith [mul_nonneg hk'.le pz]
      · constructor <;> nlinarith [mul_nonneg hk'.le py]
    apply Point3.ext <;> omega
  · obtain ⟨py0,pz0,_⟩ := hp; obtain ⟨qz0,hqb⟩ := hq
    have hqb' : (q.x : ℤ)+q.y ≤ k := by exact_mod_cast hqb
    simp only [py0,pz0,qz0,Nat.cast_zero,mul_zero,add_zero] at he
    have hy0 : q.y=0 := by
      by_contra h
      have : (1 : ℤ) ≤ q.y := by omega
      nlinarith
    apply Point3.ext <;> simp_all
  · obtain ⟨py0,pz0,_⟩ := hp; obtain ⟨qx0,_⟩ := hq
    simp only [py0,pz0,qx0,Nat.cast_zero,neg_zero,zero_add,mul_zero,add_zero] at he
    have : (q.y : ℤ)=0 ∧ (q.z : ℤ)=0 ∧ (p.x : ℤ)=0 := by
      constructor
      · nlinarith [mul_nonneg hk'.le qz]
      · constructor <;> nlinarith [mul_nonneg hk'.le qy]
    apply Point3.ext <;> omega
  · obtain ⟨py0,pz0,_⟩ := hp; obtain ⟨qy0,qz0,_⟩ := hq
    simp only [py0,pz0,qy0,qz0,Nat.cast_zero,mul_zero,add_zero] at he
    apply Point3.ext <;> omega




theorem evenIndex_bounds (L k : ℕ) (hL : k < L) {p : Point3}
    (hp : EvenRegion L k p) :
    -(L : ℤ) < evenIndex k p ∧ evenIndex k p ≤ (k : ℤ)*k+k := by
  have hL' : (k : ℤ) < L := by exact_mod_cast hL
  have hx : (0 : ℤ) ≤ p.x := by omega
  have hy : (0 : ℤ) ≤ p.y := by omega
  have hz : (0 : ℤ) ≤ p.z := by omega
  have hk : (0 : ℤ) ≤ k := by omega
  unfold evenIndex
  rcases hp with ⟨hp,hb⟩ | ⟨hp,hb⟩ | ⟨hy0,hz0,hb⟩
  · have hb' : (p.x : ℤ)+p.y ≤ k := by exact_mod_cast hb
    simp only [hp,Nat.cast_zero,mul_zero,add_zero]
    constructor <;> nlinarith [mul_nonneg hk hy, mul_nonneg hk (by omega : (0 : ℤ) ≤ k-p.y)]
  · have hb' : (p.y : ℤ)+p.z ≤ k := by exact_mod_cast hb
    simp only [hp,Nat.cast_zero,neg_zero,zero_add]
    constructor <;> nlinarith [mul_nonneg hk hy,mul_nonneg (by omega : (0 : ℤ) ≤ k+1) hz,
      mul_nonneg hk (by omega : (0 : ℤ) ≤ k-p.y-p.z)]
  · have hb' : (p.x : ℤ) < L := by exact_mod_cast hb
    simp only [hy0,hz0,Nat.cast_zero,mul_zero,add_zero]
    constructor <;> nlinarith

theorem even_residue_index (m k L a b c : ℕ)
    (ha : a+1=(k+1)*m) (hb : b=L*m+k) (hc : c=b+1) (p : Point3) :
    residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p =
      (evenIndex k p : ZMod m) := by
  have ha' := congrArg (fun n : ℕ => (n : ZMod m)) ha
  have hb' := congrArg (fun n : ℕ => (n : ZMod m)) hb
  have hc' := congrArg (fun n : ℕ => (n : ZMod m)) hc
  push_cast at ha' hb' hc'
  simp only [ZMod.natCast_self,mul_zero,zero_add] at ha' hb'
  have he : (a : ZMod m) = -1 := by linear_combination ha'
  rw [hb'] at hc'
  simp only [residueOf,evenIndex,Int.cast_add,Int.cast_neg,Int.cast_mul,Int.cast_natCast,Int.cast_one]
  rw [he,hb',hc']
  ring

theorem even_residue_injective (m k L a b c : ℕ) (hk : 0 < k)
    (hL : k < L) (hm : L+k*k+k=m)
    (ha : a+1=(k+1)*m) (hb : b=L*m+k) (hc : c=b+1)
    {p q : Point3} (hp : EvenRegion L k p) (hq : EvenRegion L k q)
    (he : residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q) : p=q := by
  rw [even_residue_index m k L a b c ha hb hc,
    even_residue_index m k L a b c ha hb hc] at he
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m).mp he
  have hp' := evenIndex_bounds L k hL hp
  have hq' := evenIndex_bounds L k hL hq
  have hm' : (L : ℤ)+(k : ℤ)*k+k=m := by exact_mod_cast hm
  have hmpos : (0 : ℤ) < m := by nlinarith
  have hh := bounded_dvd_zero hmpos
    (by omega : -(m : ℤ) < evenIndex k q-evenIndex k p)
    (by omega : evenIndex k q-evenIndex k p < m) hd
  exact evenIndex_injective L k hk hp hq (by omega)

/-- Residue-wise minimum of the numerical weight, with no tie convention. -/
def WeightMinimal (m a b c : ℕ) (p : Point3) : Prop :=
  ∀ q : Point3, residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q =
    residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p →
    aperyWeight a b c p ≤ aperyWeight a b c q

theorem weightMinimal_downward (m a b c : ℕ) {p q : Point3}
    (hpq : p ≤ q) (hq : WeightMinimal m a b c q) : WeightMinimal m a b c p := by
  obtain ⟨hx,hy,hz⟩ := hpq
  let d : Point3 := ⟨q.x-p.x,q.y-p.y,q.z-p.z⟩
  have hpd : p+d=q := by
    apply Point3.ext <;> simp [d] <;> omega
  intro u hu
  have hr : residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) (u+d) =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q := by
    rw [residueOf_add,hu,← residueOf_add,hpd]
  have hh := hq (u+d) hr
  rw [← hpd,aperyWeight_add,aperyWeight_add] at hh
  omega

private theorem not_minimal_of_drop (m a b c : ℕ) (hm : 0 < m)
    (p q : Point3) (t : ℕ) (ht : 0 < t)
    (he : aperyWeight a b c p = aperyWeight a b c q+t*m) :
    ¬ WeightMinimal m a b c p := by
  intro hp
  have he' := congrArg (fun n : ℕ => (n : ZMod m)) he
  push_cast at he'
  simp only [ZMod.natCast_self,mul_zero,add_zero] at he'
  have hr : residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p := by
    rw [← aperyWeight_cast,← aperyWeight_cast]
    exact he'.symm
  have hh := hp q hr
  nlinarith




/-- Every numerical minimum belongs to the explicit even Apéry region. -/
theorem even_weightMinimal_region (m k L a b c : ℕ) (hk : 0 < k)
    (hL : k < L) (hm : L+k*k+k=m)
    (ha : a+1=(k+1)*m) (hb : b=L*m+k) (hc : c=b+1)
    {q : Point3} (hq : WeightMinimal m a b c q) : EvenRegion L k q := by
  have hmpos : 0 < m := by nlinarith
  have hxz : ¬ WeightMinimal m a b c ⟨1,0,1⟩ := by
    apply not_minimal_of_drop m a b c hmpos ⟨1,0,1⟩ ⟨0,1,0⟩ (k+1) (by omega)
    simp only [aperyWeight]
    nlinarith
  have hxy : ∀ j r : ℕ, j+r=k → ¬ WeightMinimal m a b c ⟨j,r+1,0⟩ := by
    intro j r hjr
    apply not_minimal_of_drop m a b c hmpos ⟨j,r+1,0⟩ ⟨0,0,r⟩
      (L+(k+1)*j) (by omega)
    simp only [aperyWeight]
    nlinarith [congrArg (fun n => n*j) ha,congrArg (fun n => n*r) hc]
  have hyz : ∀ y z x : ℕ, y+z=k+1 → x+z=L → 0 < z →
      ¬ WeightMinimal m a b c ⟨0,y,z⟩ := by
    intro y z x hyz hxz hz
    apply not_minimal_of_drop m a b c hmpos ⟨0,y,z⟩ ⟨x,0,0⟩
      ((k+1)*z+1) (by omega)
    simp only [aperyWeight]
    nlinarith [congrArg (fun n => b*n) hyz,
      congrArg (fun n => ((k+1)*m)*n) hxz,
      congrArg (fun n => n*x) ha,congrArg (fun n => n*(k+1)) hb,
      congrArg (fun n => n*z) hc]
  have hxp : ¬ WeightMinimal m a b c ⟨L,0,0⟩ := by
    apply not_minimal_of_drop m a b c hmpos ⟨L,0,0⟩ ⟨0,0,k⟩
      (L-1) (by omega)
    simp only [aperyWeight]
    have hsub : L-1+1=L := by omega
    nlinarith [congrArg (fun n => n*L) ha,congrArg (fun n => n*k) hb,
      congrArg (fun n => n*k) hc,congrArg (fun n => n*m) hsub]
  have hnotxz : q.x=0 ∨ q.z=0 := by
    by_contra hh
    have hh' : (⟨1,0,1⟩ : Point3) ≤ q := by
      change 1 ≤ q.x ∧ 0 ≤ q.y ∧ 1 ≤ q.z
      omega
    exact hxz (weightMinimal_downward m a b c hh' hq)
  rcases hnotxz with hx0 | hz0
  · by_cases hsum : q.y+q.z ≤ k
    · exact Or.inr (Or.inl ⟨hx0,hsum⟩)
    · have hzpos : 0 < q.z := by
        by_contra hz
        have hle : (⟨0,k+1,0⟩ : Point3) ≤ q := by
          change 0 ≤ q.x ∧ k+1 ≤ q.y ∧ 0 ≤ q.z
          omega
        exact hxy 0 k (by omega) (weightMinimal_downward m a b c hle hq)
      let z := min q.z (k+1)
      let y := k+1-z
      let x := L-z
      have hz : z ≤ k+1 := Nat.min_le_right _ _
      have hzq : z ≤ q.z := Nat.min_le_left _ _
      have hysum : y+z=k+1 := by dsimp [y]; omega
      have hxz : x+z=L := by dsimp [x]; omega
      have hz' : 0 < z := by dsimp [z]; omega
      have hyq : y ≤ q.y := by dsimp [y,z]; omega
      have hle : (⟨0,y,z⟩ : Point3) ≤ q := ⟨Nat.zero_le _,hyq,hzq⟩
      exact False.elim (hyz y z x hysum hxz hz' (weightMinimal_downward m a b c hle hq))
  · by_cases hsum : q.x+q.y ≤ k
    · exact Or.inl ⟨hz0,hsum⟩
    · by_cases hy0 : q.y=0
      · by_cases hxL : q.x < L
        · exact Or.inr (Or.inr ⟨hy0,hz0,hxL⟩)
        · have hle : (⟨L,0,0⟩ : Point3) ≤ q := by
            change L ≤ q.x ∧ 0 ≤ q.y ∧ 0 ≤ q.z
            omega
          exact False.elim (hxp (weightMinimal_downward m a b c hle hq))
      · let j := min q.x k
        let r := k-j
        have hj : j ≤ k := Nat.min_le_right _ _
        have hjq : j ≤ q.x := Nat.min_le_left _ _
        have hjr : j+r=k := by dsimp [r]; omega
        have hrq : r+1 ≤ q.y := by dsimp [r,j]; omega
        have hle : (⟨j,r+1,0⟩ : Point3) ≤ q := ⟨hjq,hrq,Nat.zero_le _⟩
        exact False.elim (hxy j r hjr (weightMinimal_downward m a b c hle hq))




/-- A region containing all minima and having injective residues gives unique
    factorization of every point of the region, including the multiplicity coordinate. -/
theorem unique_region_factorization (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) (P : Point3 → Prop)
    (hmin : ∀ {q}, WeightMinimal m a b c q → P q)
    (hinj : ∀ {p q}, P p → P q →
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q → p=q)
    {p q : Point3} (hp : P p) (t : ℕ)
    (he : aperyWeight a b c p = t*m+aperyWeight a b c q) : t=0 ∧ q=p := by
  let r := aperyRepresentative m a b c hm hgcd
    (residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p)
  have hs := aperyRepresentative_spec m a b c hm hgcd
    (residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p)
  have hrmin : WeightMinimal m a b c r := fun u hu =>
    aperyCanonical_weight_min m a b c hs.2 hu
  have hrp : r=p := hinj (hmin hrmin) hp hs.1
  have hpmin : WeightMinimal m a b c p := hrp ▸ hrmin
  have he' := congrArg (fun n : ℕ => (n : ZMod m)) he
  push_cast at he'
  simp only [ZMod.natCast_self,mul_zero,zero_add] at he'
  have hres : residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p := by
    rw [← aperyWeight_cast,← aperyWeight_cast]
    exact he'.symm
  have hh := hpmin q hres
  have ht : t=0 := by nlinarith
  have heq : aperyWeight a b c p=aperyWeight a b c q := by simpa [ht] using he
  have hqmin : WeightMinimal m a b c q := by
    intro u hu
    rw [← heq]
    exact hpmin u (hu.trans hres)
  exact ⟨ht,hinj (hmin hqmin) hp hres⟩

theorem even_unique_factorization (m k L a b c : ℕ) (hk : 0 < k)
    (hL : k < L) (hm : L+k*k+k=m)
    (ha : a+1=(k+1)*m) (hb : b=L*m+k) (hc : c=b+1)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1)
    {p q : Point3} (hp : EvenRegion L k p) (t : ℕ)
    (he : aperyWeight a b c p=t*m+aperyWeight a b c q) : t=0 ∧ q=p := by
  apply unique_region_factorization m a b c (by nlinarith) hgcd (EvenRegion L k)
    (even_weightMinimal_region m k L a b c hk hL hm ha hb hc)
    (even_residue_injective m k L a b c hk hL hm ha hb hc) hp t he

/-- Odd case: the third-coordinate triangular face has one fewer layer. -/
def OddRegion (L k : ℕ) (p : Point3) : Prop :=
  (p.z=0 ∧ p.x+p.y ≤ k) ∨
  (p.x=0 ∧ p.y+p.z < k) ∨
  (p.y=0 ∧ p.z=0 ∧ p.x ≤ L)

theorem oddRegion_evenRegion (L k : ℕ) {p : Point3} (hp : OddRegion L k p) :
    EvenRegion (L+1) k p := by
  rcases hp with h | ⟨hx,hs⟩ | ⟨hy,hz,hx⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hx,by omega⟩)
  · exact Or.inr (Or.inr ⟨hy,hz,by omega⟩)

theorem oddIndex_bounds (L k : ℕ) (hk : 0 < k) (hL : k ≤ L) {p : Point3}
    (hp : OddRegion L k p) :
    -(L : ℤ) ≤ evenIndex k p ∧ evenIndex k p ≤ (k : ℤ)*k := by
  have hk' : (0 : ℤ) < k := by exact_mod_cast hk
  have hx : (0 : ℤ) ≤ p.x := by omega
  have hy : (0 : ℤ) ≤ p.y := by omega
  have hz : (0 : ℤ) ≤ p.z := by omega
  unfold evenIndex
  rcases hp with ⟨hp,hb⟩ | ⟨hp,hb⟩ | ⟨hy0,hz0,hb⟩
  · have hb' : (p.x : ℤ)+p.y ≤ k := by exact_mod_cast hb
    simp only [hp,Nat.cast_zero,mul_zero,add_zero]
    constructor
    · have hL' : (k : ℤ) ≤ L := by exact_mod_cast hL
      nlinarith [mul_nonneg hk'.le hy]
    · nlinarith [mul_nonneg hk'.le (by omega : (0 : ℤ) ≤ k-p.y)]
  · have hb' : (p.y : ℤ)+p.z < k := by exact_mod_cast hb
    simp only [hp,Nat.cast_zero,neg_zero,zero_add]
    constructor <;> nlinarith [mul_nonneg hk'.le hy,mul_nonneg (by omega : (0 : ℤ) ≤ k+1) hz,
      mul_nonneg hk'.le (by omega : (0 : ℤ) ≤ k-1-p.y-p.z)]
  · have hb' : (p.x : ℤ) ≤ L := by exact_mod_cast hb
    simp only [hy0,hz0,Nat.cast_zero,mul_zero,add_zero]
    constructor <;> nlinarith




theorem odd_residue_index (m k L a b c : ℕ)
    (ha : a+1=k*m) (hb : b=L*m+k) (hc : c=b+1) (p : Point3) :
    residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p =
      (evenIndex k p : ZMod m) := by
  have ha' := congrArg (fun n : ℕ => (n : ZMod m)) ha
  have hb' := congrArg (fun n : ℕ => (n : ZMod m)) hb
  have hc' := congrArg (fun n : ℕ => (n : ZMod m)) hc
  push_cast at ha' hb' hc'
  simp only [ZMod.natCast_self,mul_zero,zero_add] at ha' hb'
  have he : (a : ZMod m) = -1 := by linear_combination ha'
  rw [hb'] at hc'
  simp only [residueOf,evenIndex,Int.cast_add,Int.cast_neg,Int.cast_mul,Int.cast_natCast,Int.cast_one]
  rw [he,hb',hc']
  ring


theorem odd_residue_injective (m k L a b c : ℕ) (hk : 0 < k)
    (hL : k ≤ L) (hm : L+k*k+1=m)
    (ha : a+1=k*m) (hb : b=L*m+k) (hc : c=b+1)
    {p q : Point3} (hp : OddRegion L k p) (hq : OddRegion L k q)
    (he : residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q) : p=q := by
  rw [odd_residue_index m k L a b c ha hb hc,
    odd_residue_index m k L a b c ha hb hc] at he
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ m).mp he
  have hp' := oddIndex_bounds L k hk hL hp
  have hq' := oddIndex_bounds L k hk hL hq
  have hm' : (L : ℤ)+(k : ℤ)*k+1=m := by exact_mod_cast hm
  have hmpos : (0 : ℤ) < m := by nlinarith
  have hh := bounded_dvd_zero hmpos
    (by omega : -(m : ℤ) < evenIndex k q-evenIndex k p)
    (by omega : evenIndex k q-evenIndex k p < m) hd
  exact evenIndex_injective (L+1) k hk (oddRegion_evenRegion L k hp)
    (oddRegion_evenRegion L k hq) (by omega)

/-- Symbolic odd-family minimum characterization by positive-weight reductions. -/
theorem odd_weightMinimal_region (m k L a b c : ℕ) (hk : 2 ≤ k)
    (hL : k ≤ L) (hm : L+k*k+1=m)
    (ha : a+1=k*m) (hb : b=L*m+k) (hc : c=b+1)
    {q : Point3} (hq : WeightMinimal m a b c q) : OddRegion L k q := by
  have hmpos : 0 < m := by nlinarith
  have hxz : ¬ WeightMinimal m a b c ⟨1,0,1⟩ := by
    apply not_minimal_of_drop m a b c hmpos ⟨1,0,1⟩ ⟨0,1,0⟩ k (by omega)
    simp only [aperyWeight]
    nlinarith
  have hxy : ∀ j r : ℕ, j+r=k → 0 < j →
      ¬ WeightMinimal m a b c ⟨j,r+1,0⟩ := by
    intro j r hjr hj
    apply not_minimal_of_drop m a b c hmpos ⟨j,r+1,0⟩ ⟨0,0,r⟩
      (L+k*j) (by omega)
    simp only [aperyWeight]
    nlinarith [congrArg (fun n => n*j) ha,congrArg (fun n => n*r) hc]
  have hkm : k < m := by nlinarith
  have hyp : ¬ WeightMinimal m a b c ⟨0,k+1,0⟩ := by
    apply not_minimal_of_drop m a b c hmpos ⟨0,k+1,0⟩ ⟨L-k+1,0,0⟩
      (m-k) (by omega)
    simp only [aperyWeight]
    have hsub : L-k+1+k=L+1 := by omega
    have hsub' : m-k+k=m := by omega
    nlinarith [congrArg (fun n => n*(L-k+1)) ha,
      congrArg (fun n => n*(k+1)) hb,
      congrArg (fun n => (k*m)*n) hsub,
      congrArg (fun n => n*m) hsub']
  have hyz : ∀ y z x : ℕ, y+z=k → x+z=L+1 → 0 < z →
      ¬ WeightMinimal m a b c ⟨0,y,z⟩ := by
    intro y z x hyz hxz hz
    apply not_minimal_of_drop m a b c hmpos ⟨0,y,z⟩ ⟨x,0,0⟩
      (k*(z-1)+1) (by omega)
    simp only [aperyWeight]
    have hz' : z-1+1=z := by omega
    nlinarith [congrArg (fun n => b*n) hyz,
      congrArg (fun n => (k*m)*n) hxz,
      congrArg (fun n => n*x) ha,congrArg (fun n => n*k) hb,
      congrArg (fun n => n*z) hc,congrArg (fun n => (k*m)*n) hz']
  have hxp : ¬ WeightMinimal m a b c ⟨L+1,0,0⟩ := by
    apply not_minimal_of_drop m a b c hmpos ⟨L+1,0,0⟩ ⟨0,k,0⟩
      (k-1) (by omega)
    simp only [aperyWeight]
    have hsub : k-1+1=k := by omega
    nlinarith [congrArg (fun n => n*(L+1)) ha,congrArg (fun n => n*k) hb,
      congrArg (fun n => n*m) hsub]
  have hnotxz : q.x=0 ∨ q.z=0 := by
    by_contra hh
    have hh' : (⟨1,0,1⟩ : Point3) ≤ q := by
      change 1 ≤ q.x ∧ 0 ≤ q.y ∧ 1 ≤ q.z
      omega
    exact hxz (weightMinimal_downward m a b c hh' hq)
  rcases hnotxz with hx0 | hz0
  · by_cases hsum : q.y+q.z < k
    · exact Or.inr (Or.inl ⟨hx0,hsum⟩)
    · by_cases hzpos : 0 < q.z
      · let z := min q.z k
        let y := k-z
        let x := L+1-z
        have hz : z ≤ k := Nat.min_le_right _ _
        have hzq : z ≤ q.z := Nat.min_le_left _ _
        have hysum : y+z=k := by dsimp [y]; omega
        have hxsum : x+z=L+1 := by dsimp [x]; omega
        have hz' : 0 < z := by dsimp [z]; omega
        have hyq : y ≤ q.y := by dsimp [y,z]; omega
        have hle : (⟨0,y,z⟩ : Point3) ≤ q := ⟨Nat.zero_le _,hyq,hzq⟩
        exact False.elim (hyz y z x hysum hxsum hz' (weightMinimal_downward m a b c hle hq))
      · by_cases hsum' : q.x+q.y ≤ k
        · exact Or.inl ⟨by omega,hsum'⟩
        · have hle : (⟨0,k+1,0⟩ : Point3) ≤ q := by
            change 0 ≤ q.x ∧ k+1 ≤ q.y ∧ 0 ≤ q.z
            omega
          exact False.elim (hyp (weightMinimal_downward m a b c hle hq))
  · by_cases hsum : q.x+q.y ≤ k
    · exact Or.inl ⟨hz0,hsum⟩
    · by_cases hy0 : q.y=0
      · by_cases hxL : q.x ≤ L
        · exact Or.inr (Or.inr ⟨hy0,hz0,hxL⟩)
        · have hle : (⟨L+1,0,0⟩ : Point3) ≤ q := by
            change L+1 ≤ q.x ∧ 0 ≤ q.y ∧ 0 ≤ q.z
            omega
          exact False.elim (hxp (weightMinimal_downward m a b c hle hq))
      · by_cases hxpos : 0 < q.x
        · let j := min q.x k
          let r := k-j
          have hj : j ≤ k := Nat.min_le_right _ _
          have hjq : j ≤ q.x := Nat.min_le_left _ _
          have hj' : 0 < j := by dsimp [j]; omega
          have hjr : j+r=k := by dsimp [r]; omega
          have hrq : r+1 ≤ q.y := by dsimp [r,j]; omega
          have hle : (⟨j,r+1,0⟩ : Point3) ≤ q := ⟨hjq,hrq,Nat.zero_le _⟩
          exact False.elim (hxy j r hjr hj' (weightMinimal_downward m a b c hle hq))
        · have hle : (⟨0,k+1,0⟩ : Point3) ≤ q := by
            change 0 ≤ q.x ∧ k+1 ≤ q.y ∧ 0 ≤ q.z
            omega
          exact False.elim (hyp (weightMinimal_downward m a b c hle hq))

theorem odd_unique_factorization (m k L a b c : ℕ) (hk : 2 ≤ k)
    (hL : k ≤ L) (hm : L+k*k+1=m)
    (ha : a+1=k*m) (hb : b=L*m+k) (hc : c=b+1)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1)
    {p q : Point3} (hp : OddRegion L k p) (t : ℕ)
    (he : aperyWeight a b c p=t*m+aperyWeight a b c q) : t=0 ∧ q=p := by
  apply unique_region_factorization m a b c (by nlinarith) hgcd (OddRegion L k)
    (odd_weightMinimal_region m k L a b c hk hL hm ha hb hc)
    (odd_residue_injective m k L a b c (by omega) hL hm ha hb hc) hp t he




theorem region_canonical_iff (m a b c : ℕ) (hm : 0 < m)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) (P : Point3 → Prop)
    (hmin : ∀ {q}, WeightMinimal m a b c q → P q)
    (hinj : ∀ {p q}, P p → P q →
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p =
      residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) q → p=q)
    (p : Point3) : AperyCanonical m a b c p ↔ P p := by
  constructor
  · intro hp
    exact hmin (fun u hu => aperyCanonical_weight_min m a b c hp hu)
  · intro hp
    let r := aperyRepresentative m a b c hm hgcd
      (residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p)
    have hs := aperyRepresentative_spec m a b c hm hgcd
      (residueOf (a : ZMod m) (b : ZMod m) (c : ZMod m) p)
    have hrmin : WeightMinimal m a b c r := fun u hu =>
      aperyCanonical_weight_min m a b c hs.2 hu
    have hrp : r=p := hinj (hmin hrmin) hp hs.1
    exact hrp ▸ hs.2

theorem even_canonical_iff (m k L a b c : ℕ) (hk : 0 < k)
    (hL : k < L) (hm : L+k*k+k=m)
    (ha : a+1=(k+1)*m) (hb : b=L*m+k) (hc : c=b+1)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) (p : Point3) :
    AperyCanonical m a b c p ↔ EvenRegion L k p :=
  region_canonical_iff m a b c (by nlinarith) hgcd (EvenRegion L k)
    (even_weightMinimal_region m k L a b c hk hL hm ha hb hc)
    (even_residue_injective m k L a b c hk hL hm ha hb hc) p

theorem odd_canonical_iff (m k L a b c : ℕ) (hk : 2 ≤ k)
    (hL : k ≤ L) (hm : L+k*k+1=m)
    (ha : a+1=k*m) (hb : b=L*m+k) (hc : c=b+1)
    (hgcd : Nat.gcd m (Nat.gcd a (Nat.gcd b c))=1) (p : Point3) :
    AperyCanonical m a b c p ↔ OddRegion L k p :=
  region_canonical_iff m a b c (by nlinarith) hgcd (OddRegion L k)
    (odd_weightMinimal_region m k L a b c hk hL hm ha hb hc)
    (odd_residue_injective m k L a b c (by omega) hL hm ha hb hc) p

end NSP3.Sharpness
