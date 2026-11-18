import NSP3.V03.SpectrumRank

namespace NSP3.V03

private theorem atom_of_only_one_term (m a b c n : ℕ)
    (hn : n ∈ generatedSemigroup m a b c) (hp : 0 < n)
    (hf : ∀ t x y z, n=t*m+a*x+b*y+c*z → t+x+y+z=1) :
    SemigroupAtom (generatedSemigroup m a b c) n := by
  refine ⟨hn,hp,?_⟩
  rintro u ⟨t,x,y,z,hu⟩ v ⟨s,w,e,f,hv⟩ he
  have hh : n=(t+s)*m+a*(x+w)+b*(y+e)+c*(z+f) := by
    rw [he,hu,hv]; ring
  have hsum := hf _ _ _ _ hh
  have hs : t+x+y+z=0 ∨ s+w+e+f=0 := by omega
  rcases hs with hs | hs
  · left
    have : t=0 ∧ x=0 ∧ y=0 ∧ z=0 := by omega
    simp_all
  · right
    have : s=0 ∧ w=0 ∧ e=0 ∧ f=0 := by omega
    simp_all

/-- The explicit cardinality-four gluing candidate has four actual atoms. -/
theorem four_family_minimalFour345 (m : ℕ) (hm : 6 ≤ m) :
    MinimalFourGeneratorClass m (3*(m+1)) (4*(m+1)) (5*(m+1)) := by
  let A := m+1
  have hA : 0 < A := by dsimp [A]; omega
  have hcop : Nat.Coprime A m := by
    dsimp [A]
    rw [Nat.add_comm]
    simp
  have hsmall : ∀ d t x y z : ℕ, 3 ≤ d → d ≤ 5 →
      d*A=t*m+(3*A)*x+(4*A)*y+(5*A)*z → t+x+y+z=1 := by
    intro d t x y z hd hd' he
    have hE : d*A=t*m+A*(3*x+4*y+5*z) := by nlinarith [he]
    have ht : t < A := by
      by_contra hh
      have hta : A ≤ t := by omega
      have hmul := Nat.mul_le_mul_right m hta
      nlinarith [Nat.zero_le (A*(3*x+4*y+5*z))]
    have hdiv : A ∣ t*m := by
      have hwhole : A ∣ t*m+A*(3*x+4*y+5*z) := by
        rw [← hE]
        exact dvd_mul_left A d
      have hright : A ∣ A*(3*x+4*y+5*z) := dvd_mul_right A _
      exact (Nat.dvd_add_iff_left hright).mpr hwhole
    have htd : A ∣ t := hcop.dvd_of_dvd_mul_right hdiv
    have ht0 : t=0 := by
      by_contra hh
      have := Nat.le_of_dvd (by omega : 0 < t) htd
      omega
    have hbase : d=3*x+4*y+5*z := by nlinarith [hE]
    omega
  have hmone : ∀ t x y z : ℕ,
      m=t*m+(3*A)*x+(4*A)*y+(5*A)*z → t+x+y+z=1 := by
    intro t x y z he
    have hx : x=0 := by
      by_contra hh
      have : 1 ≤ x := by omega
      dsimp [A] at *
      nlinarith [Nat.zero_le (t*m),Nat.zero_le ((4*(m+1))*y),
        Nat.zero_le ((5*(m+1))*z)]
    have hy : y=0 := by
      by_contra hh
      have : 1 ≤ y := by omega
      dsimp [A] at *
      nlinarith [Nat.zero_le (t*m),Nat.zero_le ((3*(m+1))*x),
        Nat.zero_le ((5*(m+1))*z)]
    have hz : z=0 := by
      by_contra hh
      have : 1 ≤ z := by omega
      dsimp [A] at *
      nlinarith [Nat.zero_le (t*m),Nat.zero_le ((3*(m+1))*x),
        Nat.zero_le ((4*(m+1))*y)]
    subst x; subst y; subst z
    simp only [mul_zero,add_zero] at he
    have : t=1 := by nlinarith
    omega
  have hgcd₁ : Nat.gcd (4*A) (5*A)=A := by
    rw [Nat.gcd_mul_right]
    norm_num
  have hgcd₂ : Nat.gcd (3*A) A=A := by
    simp
  have hclassgcd : Nat.gcd m (Nat.gcd (3*A) (Nat.gcd (4*A) (5*A)))=1 := by
    rw [hgcd₁,hgcd₂]
    exact hcop.symm.gcd_eq_one
  have hg := generatedSemigroup_generators m (3*A) (4*A) (5*A)
  have hm4 : m<3*A := by dsimp [A]; omega
  have h45 : 3*A<4*A := by omega
  have h56 : 4*A<5*A := by omega
  change MinimalFourGeneratorClass m (3*A) (4*A) (5*A)
  refine ⟨?_,by omega,by dsimp [A]; omega,by dsimp [A]; omega,
    by dsimp [A]; omega,hclassgcd,?_⟩
  · have hm5 := lt_trans hm4 h45
    have hm6 := lt_trans hm5 h56
    have h46 := lt_trans h45 h56
    simp [Nat.ne_of_lt hm4, Nat.ne_of_lt hm5, Nat.ne_of_lt hm6,
      Nat.ne_of_lt h45, Nat.ne_of_lt h46, Nat.ne_of_lt h56]
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact atom_of_only_one_term _ _ _ _ _ hg.1 (by omega) hmone
    · exact atom_of_only_one_term _ _ _ _ _ hg.2.1 (by omega)
        (fun t x y z he => hsmall 3 t x y z (by omega) (by omega) he)
    · exact atom_of_only_one_term _ _ _ _ _ hg.2.2.1 (by omega)
        (fun t x y z he => hsmall 4 t x y z (by omega) (by omega) he)
    · exact atom_of_only_one_term _ _ _ _ _ hg.2.2.2 (by omega)
        (fun t x y z he => hsmall 5 t x y z (by omega) (by omega) he)


/-- The explicit cardinality-four gluing candidate has four actual atoms. -/
theorem four_family_minimalFour457 (m : ℕ) (hm : 8 ≤ m) :
    MinimalFourGeneratorClass m (4*(m+1)) (5*(m+1)) (7*(m+1)) := by
  let A := m+1
  have hA : 0 < A := by dsimp [A]; omega
  have hcop : Nat.Coprime A m := by
    dsimp [A]
    rw [Nat.add_comm]
    simp
  have hsmall : ∀ d t x y z : ℕ, 4 ≤ d → d ≤ 7 →
      d*A=t*m+(4*A)*x+(5*A)*y+(7*A)*z → t+x+y+z=1 := by
    intro d t x y z hd hd' he
    have hE : d*A=t*m+A*(4*x+5*y+7*z) := by nlinarith [he]
    have ht : t < A := by
      by_contra hh
      have hta : A ≤ t := by omega
      have hmul := Nat.mul_le_mul_right m hta
      nlinarith [Nat.zero_le (A*(4*x+5*y+7*z))]
    have hdiv : A ∣ t*m := by
      have hwhole : A ∣ t*m+A*(4*x+5*y+7*z) := by
        rw [← hE]
        exact dvd_mul_left A d
      have hright : A ∣ A*(4*x+5*y+7*z) := dvd_mul_right A _
      exact (Nat.dvd_add_iff_left hright).mpr hwhole
    have htd : A ∣ t := hcop.dvd_of_dvd_mul_right hdiv
    have ht0 : t=0 := by
      by_contra hh
      have := Nat.le_of_dvd (by omega : 0 < t) htd
      omega
    have hbase : d=4*x+5*y+7*z := by nlinarith [hE]
    omega
  have hmone : ∀ t x y z : ℕ,
      m=t*m+(4*A)*x+(5*A)*y+(7*A)*z → t+x+y+z=1 := by
    intro t x y z he
    have hx : x=0 := by
      by_contra hh
      have : 1 ≤ x := by omega
      dsimp [A] at *
      nlinarith [Nat.zero_le (t*m),Nat.zero_le ((5*(m+1))*y),
        Nat.zero_le ((7*(m+1))*z)]
    have hy : y=0 := by
      by_contra hh
      have : 1 ≤ y := by omega
      dsimp [A] at *
      nlinarith [Nat.zero_le (t*m),Nat.zero_le ((4*(m+1))*x),
        Nat.zero_le ((7*(m+1))*z)]
    have hz : z=0 := by
      by_contra hh
      have : 1 ≤ z := by omega
      dsimp [A] at *
      nlinarith [Nat.zero_le (t*m),Nat.zero_le ((4*(m+1))*x),
        Nat.zero_le ((5*(m+1))*y)]
    subst x; subst y; subst z
    simp only [mul_zero,add_zero] at he
    have : t=1 := by nlinarith
    omega
  have hgcd₁ : Nat.gcd (5*A) (7*A)=A := by
    rw [Nat.gcd_mul_right]
    norm_num
  have hgcd₂ : Nat.gcd (4*A) A=A := by
    simp
  have hclassgcd : Nat.gcd m (Nat.gcd (4*A) (Nat.gcd (5*A) (7*A)))=1 := by
    rw [hgcd₁,hgcd₂]
    exact hcop.symm.gcd_eq_one
  have hg := generatedSemigroup_generators m (4*A) (5*A) (7*A)
  have hm4 : m<4*A := by dsimp [A]; omega
  have h45 : 4*A<5*A := by omega
  have h56 : 5*A<7*A := by omega
  change MinimalFourGeneratorClass m (4*A) (5*A) (7*A)
  refine ⟨?_,by omega,by dsimp [A]; omega,by dsimp [A]; omega,
    by dsimp [A]; omega,hclassgcd,?_⟩
  · have hm5 := lt_trans hm4 h45
    have hm6 := lt_trans hm5 h56
    have h46 := lt_trans h45 h56
    simp [Nat.ne_of_lt hm4, Nat.ne_of_lt hm5, Nat.ne_of_lt hm6,
      Nat.ne_of_lt h45, Nat.ne_of_lt h46, Nat.ne_of_lt h56]
  · intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact atom_of_only_one_term _ _ _ _ _ hg.1 (by omega) hmone
    · exact atom_of_only_one_term _ _ _ _ _ hg.2.1 (by omega)
        (fun t x y z he => hsmall 4 t x y z (by omega) (by omega) he)
    · exact atom_of_only_one_term _ _ _ _ _ hg.2.2.1 (by omega)
        (fun t x y z he => hsmall 5 t x y z (by omega) (by omega) he)
    · exact atom_of_only_one_term _ _ _ _ _ hg.2.2.2 (by omega)
        (fun t x y z he => hsmall 7 t x y z (by omega) (by omega) he)


end NSP3.V03
