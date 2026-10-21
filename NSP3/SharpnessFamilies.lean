import NSP3.MinimalGeneratorClass

namespace NSP3.Sharpness

def evenA (m k : ℕ) := (k+1)*m-1
def evenB (m k : ℕ) := (m-k*k-k)*m+k
def evenC (m k : ℕ) := evenB m k+1
def oddA (m k : ℕ) := k*m-1
def oddB (m k : ℕ) := (m-k*k-1)*m+k
def oddC (m k : ℕ) := oddB m k+1

private theorem atom_of_sum_one (m a b c n : ℕ)
    (hn : n ∈ generatedSemigroup m a b c) (hp : 0  <  n)
    (hf : ∀ t x y z, n = t*m+a*x+b*y+c*z → t+x+y+z=1) :
    SemigroupAtom (generatedSemigroup m a b c) n := by
  refine ⟨hn,hp,?_⟩
  rintro u ⟨t,x,y,z,hu⟩ v ⟨s,w,e,f,hv⟩ he
  have hh : n = (t+s)*m+a*(x+w)+b*(y+e)+c*(z+f) := by
    rw [he,hu,hv]; ring
  have := hf _ _ _ _ hh
  have hs : t+x+y+z=0 ∨ s+w+e+f=0 := by omega
  rcases hs with hs | hs
  · left; have : t=0 ∧ x=0 ∧ y=0 ∧ z=0 := by omega
    simp_all
  · right; have : s=0 ∧ w=0 ∧ e=0 ∧ f=0 := by omega
    simp_all

private theorem two_generator_exclusion (m p q k a b c : ℕ)
    (hm : 0  <  m) (hk : 0  <  k) (hkm : k+1  <  m)
    (ha : a+1=p*m) (hb : b=q*m+k) (hc : c=b+1)
    (hbound : c  <  (m-k-1)*a) :
    ∀ t x, b ≠ t*m+a*x ∧ c ≠ t*m+a*x := by
  intro t x
  have hma : 0 < a := by
    by_contra h
    have hz : a=0 := by omega
    simp only [hz, mul_zero] at hbound
    omega
  have hfor : ∀ n, (n=b ∨ n=c) → n  ≤  c → n=t*m+a*x → False := by
    intro n hn hnc he
    have hxa : x*a  ≤  c := by nlinarith only [he, hnc, Nat.zero_le (t*m)]
    have hxl : x < m-k-1 := by nlinarith only [hxa,hbound,hma]
    have hlt : x+k+1 < m := by omega
    have hmul : (a+1)*x=p*m*x := congrArg (fun r => r*x) ha
    rcases hn with rfl | rfl
    · have hd0 : m ∣ q*m := by exact Nat.dvd_mul_left m q
      have hd : m ∣ q*m+(k+x) := ⟨t+p*x, by nlinarith only [he,hb,hmul]⟩
      have hd1 : m ∣ k+x := (Nat.dvd_add_iff_right hd0).mpr hd
      have := Nat.le_of_dvd (by omega : 0 < k+x) hd1
      omega
    · have hd0 : m ∣ q*m := by exact Nat.dvd_mul_left m q
      have hd : m ∣ q*m+(k+1+x) := ⟨t+p*x, by nlinarith only [he,hb,hc,hmul]⟩
      have hd1 : m ∣ k+1+x := (Nat.dvd_add_iff_right hd0).mpr hd
      have := Nat.le_of_dvd (by omega : 0 < k+1+x) hd1
      omega
  constructor
  · intro he; exact hfor b (Or.inl rfl) (by omega) he
  · intro he; exact hfor c (Or.inr rfl) le_rfl he





private theorem consecutive_class (m p q k a b c : ℕ)
    (hm : 1  <  m) (hk : 0  <  k) (hkm : k+1  <  m)
    (ha : a+1=p*m) (hb : b=q*m+k) (hc : c=b+1)
    (hma : m < a) (hab : a < b) (hbc : c < 2*b)
    (hbound : c  <  (m-k-1)*a) : MinimalFourGeneratorClass m a b c := by
  have hmp : 0 < m := by omega
  have hap : 0 < a := by omega
  have hbp : 0 < b := by omega
  have hcp : 0 < c := by omega
  have hex := two_generator_exclusion m p q k a b c hmp hk hkm ha hb hc hbound
  have hm0 : ∀ t, a ≠ t*m := by
    intro t he
    have hd0 : m ∣ a := ⟨t, by simpa [mul_comm] using he⟩
    have hd1 : m ∣ a+1 := ⟨p, by simpa [mul_comm] using ha⟩
    have hd : m ∣ 1 := (Nat.dvd_add_iff_right hd0).mpr hd1
    have := Nat.le_of_dvd (by omega : 0 < 1) hd
    omega
  have hfm : ∀ t x y z, m=t*m+a*x+b*y+c*z → t+x+y+z=1 := by
    intro t x y z he
    have hx : x=0 := by nlinarith only [he,hma,Nat.zero_le (t*m),Nat.zero_le (b*y),Nat.zero_le (c*z)]
    have hy : y=0 := by nlinarith only [he,hab,hma,Nat.zero_le (t*m),Nat.zero_le (a*x),Nat.zero_le (c*z)]
    have hz : z=0 := by nlinarith only [he,hc,hab,hma,Nat.zero_le (t*m),Nat.zero_le (a*x),Nat.zero_le (b*y)]
    subst x; subst y; subst z; simp only [mul_zero,add_zero] at he
    have : t=1 := by nlinarith only [he,hmp]
    omega
  have hfa : ∀ t x y z, a=t*m+a*x+b*y+c*z → t+x+y+z=1 := by
    intro t x y z he
    have hy : y=0 := by nlinarith only [he,hab,Nat.zero_le (t*m),Nat.zero_le (a*x),Nat.zero_le (c*z)]
    have hz : z=0 := by nlinarith only [he,hc,hab,Nat.zero_le (t*m),Nat.zero_le (a*x),Nat.zero_le (b*y)]
    subst y; subst z; simp only [mul_zero,add_zero] at he
    have hx : x ≤ 1 := by nlinarith only [he,hap,Nat.zero_le (t*m)]
    have hx1 : x=1 := by
      by_contra h; have : x=0 := by omega
      simp only [this,mul_zero,add_zero] at he
      exact hm0 t he
    subst x; simp only [mul_one] at he
    have : t=0 := by nlinarith only [he,hmp]
    omega
  have hfbc : ∀ n, (n=b ∨ n=c) → ∀ t x y z,
      n=t*m+a*x+b*y+c*z → t+x+y+z=1 := by
    intro n hn t x y z he
    have hnc : n ≤ c := by rcases hn with rfl | rfl <;> omega
    have hyz : y+z ≤ 1 := by
      nlinarith only [he,hnc,hbc,hc,hbp,Nat.zero_le (t*m),Nat.zero_le (a*x)]
    have hyz1 : y+z=1 := by
      by_contra h
      have hz : y=0 ∧ z=0 := by omega
      simp only [hz.1,hz.2,mul_zero,add_zero] at he
      rcases hn with rfl | rfl
      · exact (hex t x).1 he
      · exact (hex t x).2 he
    have htx : t=0 ∧ x=0 := by
      rcases hn with rfl | rfl
      · constructor <;> nlinarith only [he,hyz1,hc,hmp,hap]
      · by_cases hz : z=1
        · have hy : y=0 := by omega
          simp only [hz,hy,mul_one,mul_zero,add_zero] at he
          constructor <;> nlinarith only [he,hmp,hap]
        · have hy : y=1 := by omega
          have hz0 : z=0 := by omega
          simp only [hy,hz0,mul_one,mul_zero,add_zero] at he
          have hsmall : t*m+a*x=1 := by omega
          constructor <;> nlinarith only [hsmall,hm,hma]
    omega
  refine ⟨?_,hmp,by omega,by omega,by omega,?_,?_⟩
  · simp; omega
  · have hg : Nat.gcd b c=1 := by simp [hc]
    simp [hg]
  · intro g hg
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact atom_of_sum_one _ _ _ _ _ (generatedSemigroup_generators _ _ _ _).1 hmp hfm
    · exact atom_of_sum_one _ _ _ _ _ (generatedSemigroup_generators _ _ _ _).2.1 hap hfa
    · exact atom_of_sum_one _ _ _ _ _ (generatedSemigroup_generators _ _ _ _).2.2.1 hbp (hfbc _ (Or.inl rfl))
    · exact atom_of_sum_one _ _ _ _ _ (generatedSemigroup_generators _ _ _ _).2.2.2 hcp (hfbc _ (Or.inr rfl))



theorem even_minimalFour (m k : ℕ) (hk : 1 ≤ k) (hm : (k+1)^2 ≤ m) :
    MinimalFourGeneratorClass m (evenA m k) (evenB m k) (evenC m k) := by
  let p:=k+1
  let q:=m-k*k-k
  let a:=evenA m k
  let b:=evenB m k
  let c:=evenC m k
  have hm4 : 4 ≤ m := by nlinarith
  have hkm : k+1 < m := by nlinarith
  have hthreshold : k*k+k ≤ m := by nlinarith
  have hq : q+k*k+k=m := by dsimp [q]; omega
  have hqp : p ≤ q := by dsimp [p]; nlinarith [sq_nonneg k]
  have hpm : 1 ≤ (k+1)*m := by nlinarith [Nat.mul_le_mul_right m hk]
  have ha : a+1=p*m := by dsimp [a,evenA,p]; omega
  have hb : b=q*m+k := by rfl
  have hc : c=b+1 := by rfl
  have hma : m < a := by dsimp [p] at ha; nlinarith only [ha,hk,hm4]
  have hab : a < b := by nlinarith only [ha,hb,hqp,hk,hm4]
  let r:=m-k-1
  have hr : r+k+1=m := by dsimp [r]; omega
  have hdiff : q+2 ≤ r*p := by dsimp [p]; nlinarith only [hq,hr,hk,hm4]
  have hbound : c < r*a := by nlinarith only [hdiff,ha,hb,hc,hr,hm4]
  exact consecutive_class m p q k a b c (by omega) (by omega) hkm ha hb hc hma hab (by omega) hbound

theorem odd_minimalFour (m k : ℕ) (hk : 2 ≤ k) (hm : k*k+k+1 ≤ m) :
    MinimalFourGeneratorClass m (oddA m k) (oddB m k) (oddC m k) := by
  let p:=k
  let q:=m-k*k-1
  let a:=oddA m k
  let b:=oddB m k
  let c:=oddC m k
  have hm7 : 7 ≤ m := by nlinarith
  have hkm : k+1 < m := by nlinarith
  have hq : q+k*k+1=m := by dsimp [q]; omega
  have hqp : p ≤ q := by dsimp [p]; omega
  have hpm : 1 ≤ k*m := by nlinarith [Nat.mul_le_mul_right m hk]
  have ha : a+1=p*m := by dsimp [a,oddA,p]; omega
  have hb : b=q*m+k := by rfl
  have hc : c=b+1 := by rfl
  have hma : m < a := by dsimp [p] at ha; nlinarith only [ha,hk,hm7]
  have hab : a < b := by nlinarith only [ha,hb,hqp,hk,hm7]
  let r:=m-k-1
  have hr : r+k+1=m := by dsimp [r]; omega
  have hdiff : q+2 ≤ r*p := by dsimp [p]; nlinarith only [hq,hr,hk,hm7,hkm]
  have hbound : c < r*a := by nlinarith only [hdiff,ha,hb,hc,hr,hm7]
  exact consecutive_class m p q k a b c (by omega) (by omega) hkm ha hb hc hma hab (by omega) hbound

end NSP3.Sharpness






