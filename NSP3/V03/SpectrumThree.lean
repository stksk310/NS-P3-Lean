import NSP3.V03.SpectrumThreeClass

namespace NSP3.V03

private def threeRelations (A : ℕ) (p : Point3) : Finset (Fact4 × Fact4) :=
  {((0,⟨0,2,0⟩),(0,⟨1,0,1⟩)),
   ((0,⟨0,0,2⟩),(0,⟨3,0,0⟩)),
   ((A,⟨0,0,0⟩),(0,p))}

private theorem threeRelations_card (A : ℕ) (p : Point3) :
    (threeRelations A p).card ≤ 3 := by
  have h₁ := Finset.card_insert_le
    ((0,⟨0,2,0⟩),(0,⟨1,0,1⟩))
    ({((0,⟨0,0,2⟩),(0,⟨3,0,0⟩)),((A,⟨0,0,0⟩),(0,p))} : Finset (Fact4 × Fact4))
  have h₂ := Finset.card_insert_le
    ((0,⟨0,0,2⟩),(0,⟨3,0,0⟩))
    ({((A,⟨0,0,0⟩),(0,p))} : Finset (Fact4 × Fact4))
  simp only [Finset.card_singleton] at h₂
  change (threeRelations A p).card ≤ _ at h₁
  omega

private theorem base_reduce (R : Finset (Fact4 × Fact4))
    (h₅ : ((0,⟨0,2,0⟩),(0,⟨1,0,1⟩)) ∈ R)
    (h₆ : ((0,⟨0,0,2⟩),(0,⟨3,0,0⟩)) ∈ R)
    (t x y z : ℕ) : ∃ X Y Z : ℕ, Y<2 ∧ Z<2 ∧
      PresentationRel R (t,⟨x,y,z⟩) (t,⟨X,Y,Z⟩) := by
  have hall : ∀ n : ℕ, ∀ t x y z : ℕ, y+z=n →
      ∃ X Y Z : ℕ, Y<2 ∧ Z<2 ∧
        PresentationRel R (t,⟨x,y,z⟩) (t,⟨X,Y,Z⟩) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t x y z hn
      by_cases hy : y<2
      · by_cases hz : z<2
        · exact ⟨x,y,z,hy,hz,PresentationRel.refl _⟩
        · have hedge := PresentationRel.context (PresentationRel.edge h₆) (t,⟨x,y,z-2⟩)
          have he : PresentationRel R (t,⟨x,y,z⟩) (t,⟨x+3,y,z-2⟩) := by
            convert hedge using 1 <;> ext <;> simp <;> omega
          obtain ⟨X,Y,Z,hY,hZ,hr⟩ := ih (y+(z-2)) (by omega) t (x+3) y (z-2) rfl
          exact ⟨X,Y,Z,hY,hZ,PresentationRel.trans he hr⟩
      · have hedge := PresentationRel.context (PresentationRel.edge h₅) (t,⟨x,y-2,z⟩)
        have he : PresentationRel R (t,⟨x,y,z⟩) (t,⟨x+1,y-2,z+1⟩) := by
          convert hedge using 1 <;> ext <;> simp <;> omega
        obtain ⟨X,Y,Z,hY,hZ,hr⟩ := ih ((y-2)+(z+1)) (by omega) t (x+1) (y-2) (z+1) rfl
        exact ⟨X,Y,Z,hY,hZ,PresentationRel.trans he hr⟩
  exact hall (y+z) t x y z rfl

private theorem three_reduce (A : ℕ) (hA : 0 < A) (p : Point3)
    (t : ℕ) (q : Point3) : ∃ T X Y Z : ℕ, T<A ∧ Y<2 ∧ Z<2 ∧
      PresentationRel (threeRelations A p) (t,q) (T,⟨X,Y,Z⟩) := by
  have h₅ : ((0,⟨0,2,0⟩),(0,⟨1,0,1⟩)) ∈ threeRelations A p := by
    simp [threeRelations]
  have h₆ : ((0,⟨0,0,2⟩),(0,⟨3,0,0⟩)) ∈ threeRelations A p := by
    simp [threeRelations]
  have hglue : ((A,⟨0,0,0⟩),(0,p)) ∈ threeRelations A p := by
    simp [threeRelations]
  induction t using Nat.strong_induction_on generalizing q with
  | h t ih =>
    by_cases ht : t<A
    · obtain ⟨X,Y,Z,hY,hZ,hr⟩ := base_reduce _ h₅ h₆ t q.x q.y q.z
      exact ⟨t,X,Y,Z,ht,hY,hZ,by simpa using hr⟩
    · have hedge := PresentationRel.context (PresentationRel.edge hglue) (t-A,q)
      have he : PresentationRel (threeRelations A p) (t,q) (t-A,p+q) := by
        change PresentationRel (threeRelations A p)
          (A+(t-A),(⟨0,0,0⟩ : Point3)+q) (0+(t-A),p+q) at hedge
        have hc : A+(t-A)=t := by omega
        have hz : (⟨0,0,0⟩ : Point3)+q=q := by ext <;> simp
        simpa only [hc,hz,Nat.zero_add] using hedge
      obtain ⟨T,X,Y,Z,hT,hY,hZ,hr⟩ := ih (t-A) (by omega) (p+q)
      exact ⟨T,X,Y,Z,hT,hY,hZ,PresentationRel.trans he hr⟩

private theorem small_dvd_difference_zero (A t u : ℕ) (hA : 0 < A)
    (ht : t<A) (hu : u<A) (hd : (A : ℤ) ∣ (t : ℤ)-u) : t=u := by
  obtain ⟨k,hk⟩ := hd
  have hA' : (0 : ℤ)<A := by omega
  have ht' : (t : ℤ)<A := by exact_mod_cast ht
  have hu' : (u : ℤ)<A := by exact_mod_cast hu
  have ht0 : (0 : ℤ) ≤ t := by omega
  have hu0 : (0 : ℤ) ≤ u := by omega
  by_cases hz : k=0
  · simp [hz] at hk
    omega
  · by_cases hp : 0<k
    · have : 1≤k := by omega
      nlinarith
    · have : k≤-1 := by omega
      nlinarith

private theorem three_reduced_unique (m t u x y z X Y Z : ℕ)
    (ht : t < m + 1) (hu : u < m + 1) (hy : y<2) (hz : z<2) (hY : Y<2) (hZ : Z<2)
    (he : factorWeight m (4*(m+1)) (5*(m+1)) (6*(m+1)) (t,⟨x,y,z⟩) =
      factorWeight m (4*(m+1)) (5*(m+1)) (6*(m+1)) (u,⟨X,Y,Z⟩)) :
    ((t,⟨x,y,z⟩) : Fact4)=(u,⟨X,Y,Z⟩) := by
  have heN : t*m+4*(m+1)*x+5*(m+1)*y+6*(m+1)*z =
      u*m+4*(m+1)*X+5*(m+1)*Y+6*(m+1)*Z := by
    simpa [factorWeight,aperyWeight,add_assoc] using he
  have he' : (t : ℤ)*m+4*(m+1)*x+5*(m+1)*y+6*(m+1)*z =
      (u : ℤ)*m+4*(m+1)*X+5*(m+1)*Y+6*(m+1)*Z := by
    exact_mod_cast heN
  have hd : ((m+1 : ℕ) : ℤ) ∣ (t : ℤ)-u := by
    refine ⟨(t : ℤ)-u+4*(x : ℤ)+5*y+6*z-4*X-5*Y-6*Z,?_⟩
    push_cast
    nlinarith [he']
  have htu := small_dvd_difference_zero (m+1) t u (by omega) ht hu hd
  subst u
  have hbase : 4*x+5*y+6*z=4*X+5*Y+6*Z := by
    have hmul : (m+1)*(4*x+5*y+6*z)=(m+1)*(4*X+5*Y+6*Z) := by
      dsimp [factorWeight,aperyWeight] at he
      nlinarith [he]
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m + 1) hmul
  have hcoords : x=X ∧ y=Y ∧ z=Z := by omega
  rcases hcoords with ⟨rfl,rfl,rfl⟩
  rfl

private theorem threeRelations_present (m : ℕ) (p : Point3)
    (hp : m=4*p.x+5*p.y+6*p.z) :
    IsFactorPresentation m (4*(m+1)) (5*(m+1)) (6*(m+1))
      (threeRelations (m+1) p) := by
  have hsound : ∀ e ∈ threeRelations (m+1) p,
      factorWeight m (4*(m+1)) (5*(m+1)) (6*(m+1)) e.1 =
      factorWeight m (4*(m+1)) (5*(m+1)) (6*(m+1)) e.2 := by
    intro e he
    simp only [threeRelations, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl
    · simp [factorWeight,aperyWeight]; ring
    · simp [factorWeight,aperyWeight]; ring
    · simp [factorWeight,aperyWeight]
      nlinarith [hp]
  intro a b
  constructor
  · exact presentationRel_sound _ _ _ _ _ hsound
  · intro he
    obtain ⟨T,X,Y,Z,hT,hY,hZ,ha⟩ := three_reduce (m+1) (by omega) p a.1 a.2
    obtain ⟨U,V,W,Q,hU,hW,hQ,hb⟩ := three_reduce (m+1) (by omega) p b.1 b.2
    have hval := (presentationRel_sound _ _ _ _ _ hsound ha).symm.trans
      (he.trans (presentationRel_sound _ _ _ _ _ hsound hb))
    have heq := three_reduced_unique m T U X Y Z V W Q hT hU hY hZ hW hQ hval
    rw [← heq] at hb
    exact PresentationRel.trans ha (PresentationRel.symm hb)

/-- Cardinality three is genuinely attained at every multiplicity at least eight. -/
theorem spectrum_three_exists (m : ℕ) (hm : 8 ≤ m) : 3 ∈ sharpRhoValues m := by
  have hclass := three_family_minimalFour m hm
  obtain ⟨x,y,z,hxyz⟩ := four_five_six_representation m hm
  have hp : m=4*(⟨x,y,z⟩ : Point3).x+5*(⟨x,y,z⟩ : Point3).y+
      6*(⟨x,y,z⟩ : Point3).z := hxyz
  have hrho : intrinsicRho (generatedSemigroup m (4*(m+1)) (5*(m+1)) (6*(m+1)))=3 := by
    apply le_antisymm ?_ (intrinsicRho_ge_three _ _ _ _ hclass)
    rw [literature_rho_identification _ _ _ _ hclass]
    exact (minimumFourInputRelations_le _ _ _ _ _ (threeRelations_present m _ hp)).trans
      (threeRelations_card _ _)
  have hs := minimal_generator_class_bridge _ _ _ _ hclass
  exact ⟨generatedAddSubmonoid m (4*(m+1)) (5*(m+1)) (6*(m+1)),
    hs.2.2.2,hs.2.2.1,hs.1,hrho⟩

end NSP3.V03
