import NSP3.GeneratedSemigroupApery
import NSP3.SharpnessAssembly

namespace NSP3.V03

open NSP3.Sharpness NSP3.CommonCard

private theorem zero_coefficients (m a b c t x y z : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : t*m+a*x+b*y+c*z=0) : t=0 ∧ x=0 ∧ y=0 ∧ z=0 := by
  have ht : t*m=0 := by omega
  have hx : a*x=0 := by omega
  have hy : b*y=0 := by omega
  have hz : c*z=0 := by omega
  exact ⟨(mul_eq_zero.mp ht).resolve_right (Nat.ne_of_gt hm),
    (mul_eq_zero.mp hx).resolve_left (Nat.ne_of_gt ha),
    (mul_eq_zero.mp hy).resolve_left (Nat.ne_of_gt hb),
    (mul_eq_zero.mp hz).resolve_left (Nat.ne_of_gt hc)⟩

/-- A factorization of an actual atom contains precisely one generator term. -/
theorem atom_coefficients_sum_one (m a b c n t x y z : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hn : SemigroupAtom (generatedSemigroup m a b c) n)
    (he : n=t*m+a*x+b*y+c*z) : t+x+y+z=1 := by
  have hg := generatedSemigroup_generators m a b c
  have hdrop (g u : ℕ) (hgm : g∈generatedSemigroup m a b c)
      (hgp : 0<g) (hum : u∈generatedSemigroup m a b c)
      (heq : n=g+u) : u=0 := by
    rcases hn.2.2 g hgm u hum heq with h | h
    · omega
    · exact h
  cases t with
  | succ t =>
    have hu : t*m+a*x+b*y+c*z∈generatedSemigroup m a b c := ⟨t,x,y,z,rfl⟩
    have hz := hdrop m _ hg.1 hm hu (by
      rw [he]
      try simp only [Nat.succ_eq_add_one]
      ring)
    obtain ⟨ht,hx,hy,hz⟩ := zero_coefficients m a b c t x y z hm ha hb hc hz
    simp [ht,hx,hy,hz]
  | zero =>
    cases x with
    | succ x =>
      have hu : 0*m+a*x+b*y+c*z∈generatedSemigroup m a b c := ⟨0,x,y,z,rfl⟩
      have hz := hdrop a _ hg.2.1 ha hu (by
        rw [he]
        try simp only [Nat.succ_eq_add_one]
        ring)
      obtain ⟨_,hx,hy,hz⟩ := zero_coefficients m a b c 0 x y z hm ha hb hc hz
      simp [hx,hy,hz]
    | zero =>
      cases y with
      | succ y =>
        have hu : 0*m+a*0+b*y+c*z∈generatedSemigroup m a b c := ⟨0,0,y,z,rfl⟩
        have hz := hdrop b _ hg.2.2.1 hb hu (by
          rw [he]
          try simp only [Nat.succ_eq_add_one]
          ring)
        obtain ⟨_,_,hy,hz⟩ := zero_coefficients m a b c 0 0 y z hm ha hb hc hz
        simp [hy,hz]
      | zero =>
        cases z with
        | zero => simp at he; exact False.elim (by have := hn.2.1; omega)
        | succ z =>
          have hu : 0*m+a*0+b*0+c*z∈generatedSemigroup m a b c := ⟨0,0,0,z,rfl⟩
          have hz := hdrop c _ hg.2.2.2 hc hu (by
            rw [he]
            try simp only [Nat.succ_eq_add_one]
            ring)
          obtain ⟨_,_,_,hz⟩ := zero_coefficients m a b c 0 0 0 z hm ha hb hc hz
          simp [hz]

theorem input_weights_injective (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) : Function.Injective ![m,a,b,c] := by
  have hnd := h.distinct
  simp at hnd
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Genuine atom factorization uniqueness in the original four-coordinate monoid. -/
theorem input_atom_unique (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (j : Fin 4) (w : FourCoeff)
    (he : degree ![m,a,b,c] (Pi.single j 1)=degree ![m,a,b,c] w) :
    w=Pi.single j 1 := by
  have ha : 0<a := lt_of_lt_of_le h.positive h.least_a
  have hb : 0<b := lt_of_lt_of_le h.positive h.least_b
  have hc : 0<c := lt_of_lt_of_le h.positive h.least_c
  have hn : SemigroupAtom (generatedSemigroup m a b c) (![m,a,b,c] j) :=
    h.atoms _ (by fin_cases j <;> simp)
  have he' : ![m,a,b,c] j=w 0*m+a*w 1+b*w 2+c*w 3 := by
    simpa [degree_single,degree_four_parts,aperyWeight,add_assoc] using he
  have hsum := atom_coefficients_sum_one m a b c _ _ _ _ _ h.positive ha hb hc hn he'
  have hcases :
      (w 0=1 ∧ w 1=0 ∧ w 2=0 ∧ w 3=0) ∨
      (w 0=0 ∧ w 1=1 ∧ w 2=0 ∧ w 3=0) ∨
      (w 0=0 ∧ w 1=0 ∧ w 2=1 ∧ w 3=0) ∨
      (w 0=0 ∧ w 1=0 ∧ w 2=0 ∧ w 3=1) := by omega
  have hex : ∃ i : Fin 4, w=Pi.single i 1 := by
    rcases hcases with hh | hh | hh | hh
    · obtain ⟨h0,h1,h2,h3⟩ := hh
      refine ⟨0,?_⟩
      funext i
      fin_cases i <;> simp [Pi.single_apply,h0,h1,h2,h3]
    · obtain ⟨h0,h1,h2,h3⟩ := hh
      refine ⟨1,?_⟩
      funext i
      fin_cases i <;> simp [Pi.single_apply,h0,h1,h2,h3]
    · obtain ⟨h0,h1,h2,h3⟩ := hh
      refine ⟨2,?_⟩
      funext i
      fin_cases i <;> simp [Pi.single_apply,h0,h1,h2,h3]
    · obtain ⟨h0,h1,h2,h3⟩ := hh
      refine ⟨3,?_⟩
      funext i
      fin_cases i <;> simp [Pi.single_apply,h0,h1,h2,h3]
  obtain ⟨i,hi⟩ := hex
  have hij : ![m,a,b,c] j=![m,a,b,c] i := by
    simpa [hi,degree_single] using he
  have hji := input_weights_injective m a b c h hij
  simpa [hji] using hi

end NSP3.V03
