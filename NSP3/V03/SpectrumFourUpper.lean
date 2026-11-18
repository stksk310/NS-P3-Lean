import NSP3.V03.SpectrumFourClass
import NSP3.V03.SpectrumGluing

namespace NSP3.V03

def fourRelations345 (A : ℕ) (p : Point3) : Finset (Fact4 × Fact4) :=
  {((0,⟨0,2,0⟩),(0,⟨1,0,1⟩)),
   ((0,⟨0,1,1⟩),(0,⟨3,0,0⟩)),
   ((0,⟨0,0,2⟩),(0,⟨2,1,0⟩)),
   ((A,⟨0,0,0⟩),(0,p))}

def fourRelations457 (A : ℕ) (p : Point3) : Finset (Fact4 × Fact4) :=
  {((0,⟨0,1,1⟩),(0,⟨3,0,0⟩)),
   ((0,⟨0,0,2⟩),(0,⟨1,2,0⟩)),
   ((0,⟨0,3,0⟩),(0,⟨2,0,1⟩)),
   ((A,⟨0,0,0⟩),(0,p))}

theorem fourRelations345_card (A : ℕ) (p : Point3) : (fourRelations345 A p).card≤4 :=
  Finset.card_le_four

theorem fourRelations457_card (A : ℕ) (p : Point3) : (fourRelations457 A p).card≤4 :=
  Finset.card_le_four

private def Reduced345 (p : Point3) : Prop :=
  p.y<2 ∧ p.z<2 ∧ p.y+p.z<2

private def Reduced457 (p : Point3) : Prop :=
  p.y<3 ∧ p.z<2 ∧ (p.y=0 ∨ p.z=0)

private theorem reduce345 (R : Finset (Fact4 × Fact4))
    (hyy : ((0,⟨0,2,0⟩),(0,⟨1,0,1⟩))∈R)
    (hyz : ((0,⟨0,1,1⟩),(0,⟨3,0,0⟩))∈R)
    (hzz : ((0,⟨0,0,2⟩),(0,⟨2,1,0⟩))∈R)
    (t : ℕ) (q : Point3) :
    ∃ r, Reduced345 r ∧ PresentationRel R (t,q) (t,r) := by
  have hall : ∀ n : ℕ, ∀ t x y z : ℕ, y+z=n →
      ∃ r, Reduced345 r ∧ PresentationRel R (t,⟨x,y,z⟩) (t,r) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t x y z hn
      by_cases hy : 2≤y
      · have hedge := PresentationRel.context (PresentationRel.edge hyy) (t,⟨x,y-2,z⟩)
        have he : PresentationRel R (t,⟨x,y,z⟩) (t,⟨x+1,y-2,z+1⟩) := by
          convert hedge using 1 <;> ext <;> simp <;> omega
        obtain ⟨r,hr,hrel⟩ := ih ((y-2)+(z+1)) (by omega) t (x+1) (y-2) (z+1) rfl
        exact ⟨r,hr,PresentationRel.trans he hrel⟩
      · by_cases hz : 2≤z
        · have hedge := PresentationRel.context (PresentationRel.edge hzz) (t,⟨x,y,z-2⟩)
          have he : PresentationRel R (t,⟨x,y,z⟩) (t,⟨x+2,y+1,z-2⟩) := by
            convert hedge using 1 <;> ext <;> simp <;> omega
          obtain ⟨r,hr,hrel⟩ := ih ((y+1)+(z-2)) (by omega) t (x+2) (y+1) (z-2) rfl
          exact ⟨r,hr,PresentationRel.trans he hrel⟩
        · by_cases hyz' : 1≤y ∧ 1≤z
          · have hedge := PresentationRel.context (PresentationRel.edge hyz) (t,⟨x,y-1,z-1⟩)
            have he : PresentationRel R (t,⟨x,y,z⟩) (t,⟨x+3,y-1,z-1⟩) := by
              convert hedge using 1 <;> ext <;> simp <;> omega
            obtain ⟨r,hr,hrel⟩ := ih ((y-1)+(z-1)) (by omega) t (x+3) (y-1) (z-1) rfl
            exact ⟨r,hr,PresentationRel.trans he hrel⟩
          · exact ⟨⟨x,y,z⟩,by dsimp [Reduced345]; omega,PresentationRel.refl _⟩
  exact hall (q.y+q.z) t q.x q.y q.z rfl

private theorem reduce457 (R : Finset (Fact4 × Fact4))
    (hyz : ((0,⟨0,1,1⟩),(0,⟨3,0,0⟩))∈R)
    (hzz : ((0,⟨0,0,2⟩),(0,⟨1,2,0⟩))∈R)
    (hyyy : ((0,⟨0,3,0⟩),(0,⟨2,0,1⟩))∈R)
    (t : ℕ) (q : Point3) :
    ∃ r, Reduced457 r ∧ PresentationRel R (t,q) (t,r) := by
  have hall : ∀ n : ℕ, ∀ t x y z : ℕ, 2*y+3*z=n →
      ∃ r, Reduced457 r ∧ PresentationRel R (t,⟨x,y,z⟩) (t,r) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t x y z hn
      by_cases hy : 3≤y
      · have hedge := PresentationRel.context (PresentationRel.edge hyyy) (t,⟨x,y-3,z⟩)
        have he : PresentationRel R (t,⟨x,y,z⟩) (t,⟨x+2,y-3,z+1⟩) := by
          convert hedge using 1 <;> ext <;> simp <;> omega
        obtain ⟨r,hr,hrel⟩ := ih (2*(y-3)+3*(z+1)) (by omega) t (x+2) (y-3) (z+1) rfl
        exact ⟨r,hr,PresentationRel.trans he hrel⟩
      · by_cases hz : 2≤z
        · have hedge := PresentationRel.context (PresentationRel.edge hzz) (t,⟨x,y,z-2⟩)
          have he : PresentationRel R (t,⟨x,y,z⟩) (t,⟨x+1,y+2,z-2⟩) := by
            convert hedge using 1 <;> ext <;> simp <;> omega
          obtain ⟨r,hr,hrel⟩ := ih (2*(y+2)+3*(z-2)) (by omega) t (x+1) (y+2) (z-2) rfl
          exact ⟨r,hr,PresentationRel.trans he hrel⟩
        · by_cases hyz' : 1≤y ∧ 1≤z
          · have hedge := PresentationRel.context (PresentationRel.edge hyz) (t,⟨x,y-1,z-1⟩)
            have he : PresentationRel R (t,⟨x,y,z⟩) (t,⟨x+3,y-1,z-1⟩) := by
              convert hedge using 1 <;> ext <;> simp <;> omega
            obtain ⟨r,hr,hrel⟩ := ih (2*(y-1)+3*(z-1)) (by omega) t (x+3) (y-1) (z-1) rfl
            exact ⟨r,hr,PresentationRel.trans he hrel⟩
          · exact ⟨⟨x,y,z⟩,by dsimp [Reduced457]; omega,PresentationRel.refl _⟩
  exact hall (2*q.y+3*q.z) t q.x q.y q.z rfl

private theorem scaled_factorWeight (m a b c : ℕ) (u : Fact4) :
    factorWeight m (a*(m+1)) (b*(m+1)) (c*(m+1)) u =
      u.1*m+(m+1)*aperyWeight a b c u.2 := by
  simp only [factorWeight,aperyWeight]
  ring

private theorem scaled_presentation (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (p : Point3) (P : Point3 → Prop)
    (hbase : ∀ t q, ∃ r, P r ∧ PresentationRel R (t,q) (t,r))
    (hglue : ((m+1,⟨0,0,0⟩),(0,p))∈R)
    (hunique : ∀ r s, P r → P s → aperyWeight a b c r=aperyWeight a b c s → r=s)
    (hsound : ∀ e∈R,
      factorWeight m (a*(m+1)) (b*(m+1)) (c*(m+1)) e.1 =
      factorWeight m (a*(m+1)) (b*(m+1)) (c*(m+1)) e.2) :
    IsFactorPresentation m (a*(m+1)) (b*(m+1)) (c*(m+1)) R := by
  intro u v
  constructor
  · exact presentationRel_sound _ _ _ _ _ hsound
  · intro he
    obtain ⟨T,r,hT,hr,hu⟩ :=
      normalize_gluing_coefficient R (m+1) (by omega) p P hbase hglue u.1 u.2
    obtain ⟨U,s,hU,hs,hv⟩ :=
      normalize_gluing_coefficient R (m+1) (by omega) p P hbase hglue v.1 v.2
    have hw := (presentationRel_sound _ _ _ _ _ hsound hu).symm.trans
      (he.trans (presentationRel_sound _ _ _ _ _ hsound hv))
    rw [scaled_factorWeight,scaled_factorWeight] at hw
    have hTU := gluing_coefficient_eq m T U _ _ hT hU hw
    subst U
    have hmul : (m+1)*aperyWeight a b c r=(m+1)*aperyWeight a b c s :=
      Nat.add_left_cancel hw
    have heq := hunique r s hr hs (Nat.eq_of_mul_eq_mul_left (by omega) hmul)
    subst s
    exact PresentationRel.trans hu (PresentationRel.symm hv)

theorem fourRelations345_present (m : ℕ) (p : Point3)
    (hp : m=3*p.x+4*p.y+5*p.z) :
    IsFactorPresentation m (3*(m+1)) (4*(m+1)) (5*(m+1))
      (fourRelations345 (m+1) p) := by
  apply scaled_presentation m 3 4 5 _ p Reduced345
  · intro t q
    exact reduce345 _ (by simp [fourRelations345]) (by simp [fourRelations345])
      (by simp [fourRelations345]) t q
  · simp [fourRelations345]
  · intro r s hr hs he
    rcases r with ⟨x,y,z⟩
    rcases s with ⟨X,Y,Z⟩
    dsimp [Reduced345,aperyWeight] at hr hs he
    rcases hr with ⟨hy,hz,hyz⟩
    rcases hs with ⟨hY,hZ,hYZ⟩
    interval_cases y <;> interval_cases z <;>
      interval_cases Y <;> interval_cases Z <;>
      simp_all [Point3.mk.injEq] <;> omega
  · intro e he
    simp only [fourRelations345,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · simp [factorWeight,aperyWeight]; ring
    · simp [factorWeight,aperyWeight]; ring
    · simp [factorWeight,aperyWeight]; ring
    · simp [factorWeight,aperyWeight]
      nlinarith [hp]

theorem fourRelations457_present (m : ℕ) (p : Point3)
    (hp : m=4*p.x+5*p.y+7*p.z) :
    IsFactorPresentation m (4*(m+1)) (5*(m+1)) (7*(m+1))
      (fourRelations457 (m+1) p) := by
  apply scaled_presentation m 4 5 7 _ p Reduced457
  · intro t q
    exact reduce457 _ (by simp [fourRelations457]) (by simp [fourRelations457])
      (by simp [fourRelations457]) t q
  · simp [fourRelations457]
  · intro r s hr hs he
    rcases r with ⟨x,y,z⟩
    rcases s with ⟨X,Y,Z⟩
    dsimp [Reduced457,aperyWeight] at hr hs he
    rcases hr with ⟨hy,hz,hyz⟩
    rcases hs with ⟨hY,hZ,hYZ⟩
    interval_cases y <;> interval_cases z <;>
      interval_cases Y <;> interval_cases Z <;>
      simp_all [Point3.mk.injEq] <;> omega
  · intro e he
    simp only [fourRelations457,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl
    · simp [factorWeight,aperyWeight]; ring
    · simp [factorWeight,aperyWeight]; ring
    · simp [factorWeight,aperyWeight]; ring
    · simp [factorWeight,aperyWeight]
      nlinarith [hp]

theorem three_four_five_representation (m : ℕ) (hm : 6 ≤ m) :
    ∃ x y z : ℕ, m=3*x+4*y+5*z := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hs : m≤8
    · interval_cases m
      · exact ⟨2,0,0,by norm_num⟩
      · exact ⟨1,1,0,by norm_num⟩
      · exact ⟨1,0,1,by norm_num⟩
    · obtain ⟨x,y,z,he⟩ := ih (m-3) (by omega) (by omega)
      exact ⟨x+1,y,z,by omega⟩

theorem rho_four345_le_four (m : ℕ) (hm : 6 ≤ m) :
    intrinsicRho (generatedSemigroup m (3*(m+1)) (4*(m+1)) (5*(m+1)))≤4 := by
  have hclass := four_family_minimalFour345 m hm
  obtain ⟨x,y,z,hxyz⟩ := three_four_five_representation m hm
  have hp : m=3*(⟨x,y,z⟩ : Point3).x+4*(⟨x,y,z⟩ : Point3).y+
      5*(⟨x,y,z⟩ : Point3).z := hxyz
  rw [literature_rho_identification _ _ _ _ hclass]
  exact (minimumFourInputRelations_le _ _ _ _ _ (fourRelations345_present m _ hp)).trans
    (fourRelations345_card _ _)

theorem rho_four457_le_four (m : ℕ) (hm : 8 ≤ m) (p : Point3)
    (hp : m=4*p.x+5*p.y+7*p.z) :
    intrinsicRho (generatedSemigroup m (4*(m+1)) (5*(m+1)) (7*(m+1)))≤4 := by
  have hclass := four_family_minimalFour457 m hm
  rw [literature_rho_identification _ _ _ _ hclass]
  exact (minimumFourInputRelations_le _ _ _ _ _ (fourRelations457_present m p hp)).trans
    (fourRelations457_card _ _)

end NSP3.V03
