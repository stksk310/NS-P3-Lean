import NSP3.V03.SpectrumFourUpper
import NSP3.V03.MultiIsolated

namespace NSP3.V03
open NSP3.CommonCard NSP3.Sharpness Finset

set_option maxHeartbeats 4000000

/-- Small base degrees cannot acquire a nonzero gluing coefficient. -/
theorem glued_small_unique (m a b c : ℕ) (p : Point3)
    (hsmall : aperyWeight a b c p < m)
    (hunique : ∀ q,aperyWeight a b c q=aperyWeight a b c p→q=p)
    (t : ℕ) (q : Point3)
    (he : aperyWeight (a*(m+1)) (b*(m+1)) (c*(m+1)) p=
      t*m+aperyWeight (a*(m+1)) (b*(m+1)) (c*(m+1)) q) :
    t=0 ∧ q=p := by
  let d := aperyWeight a b c p
  let Q := aperyWeight a b c q
  have he' : 0*m+(m+1)*d=t*m+(m+1)*Q := by
    dsimp [d,Q,aperyWeight] at *
    nlinarith only [he]
  have ht : t < m+1 := by
    by_contra hh
    have hge : m+1 ≤ t := by omega
    have hmul := Nat.mul_le_mul_right m hge
    dsimp [d] at he'
    nlinarith only [he',hmul,hsmall,Nat.zero_le ((m+1)*Q)]
  have ht0 : t=0 := (gluing_coefficient_eq m 0 t d Q (by omega) ht he').symm
  have hQ : Q=d := by
    rw [ht0] at he'
    have hc : (m+1)*d=(m+1)*Q := by simpa using he'
    exact (Nat.eq_of_mul_eq_mul_left (by omega : 0 < m+1) hc).symm
  exact ⟨ht0,hunique q hQ⟩

def pureMultiplicity (m : ℕ) : FourCoeff := ![m+1,0,0,0]

/-- The pure gluing factorization is isolated; only its one predecessor is used. -/
theorem pureMultiplicity_isolated (m a b c : ℕ) (hm : 0 < m)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (v : FourCoeff)
    (he : BaseEdge ![m,a*(m+1),b*(m+1),c*(m+1)]
      (degree ![m,a*(m+1),b*(m+1),c*(m+1)] (pureMultiplicity m))
      (pureMultiplicity m) v) : v=pureMultiplicity m := by
  apply base_isolated_of_unique_predecessors _ _ ?_ v he
  intro i hi w hw
  fin_cases i
  · have hsub : pureMultiplicity m-Pi.single (0 : Fin 4) 1=![m,0,0,0] := by
      funext j
      fin_cases j <;> simp [pureMultiplicity,Pi.single_apply]
    change degree ![m,a*(m+1),b*(m+1),c*(m+1)]
      (pureMultiplicity m-Pi.single (0 : Fin 4) 1)=
      degree ![m,a*(m+1),b*(m+1),c*(m+1)] w at hw
    change w=pureMultiplicity m-Pi.single (0 : Fin 4) 1
    rw [hsub] at hw ⊢
    let Q := a*w 1+b*w 2+c*w 3
    have he' : m*m+(m+1)*0=(w 0)*m+(m+1)*Q := by
      rw [degree_four_parts,degree_four_parts] at hw
      simp only [aperyWeight] at hw
      change m*m=(w 0)*m+
        (a*(m+1)*w 1+b*(m+1)*w 2+c*(m+1)*w 3) at hw
      dsimp [Q]
      nlinarith only [hw]
    have hlt : w 0 < m+1 := by
      by_contra hh
      have hge : m+1 ≤ w 0 := by omega
      have hmul := Nat.mul_le_mul_right m hge
      nlinarith only [he',hmul,hm,Nat.zero_le ((m+1)*Q)]
    have hw0 : w 0=m :=
      (gluing_coefficient_eq m m (w 0) 0 Q (by omega) hlt he').symm
    have hQmul : (m+1)*Q=0 := by rw [hw0] at he'; omega
    have hQ : Q=0 := (mul_eq_zero.mp hQmul).resolve_left (by omega)
    change a*w 1+b*w 2+c*w 3=0 at hQ
    have hw1 : w 1=0 := (mul_eq_zero.mp (show a*w 1=0 by omega)).resolve_left (by omega)
    have hw2 : w 2=0 := (mul_eq_zero.mp (show b*w 2=0 by omega)).resolve_left (by omega)
    have hw3 : w 3=0 := (mul_eq_zero.mp (show c*w 3=0 by omega)).resolve_left (by omega)
    funext j
    fin_cases j <;> simp [hw0,hw1,hw2,hw3]
  · simp [pureMultiplicity] at hi
  · simp [pureMultiplicity] at hi
  · simp [pureMultiplicity] at hi

def four345Atom (p : Point3) : Prop :=
  p=⟨1,0,0⟩ ∨ p=⟨0,1,0⟩ ∨ p=⟨0,0,1⟩

theorem four345_atom_unique (m : ℕ) (hm : 6 ≤ m) (p : Point3)
    (hp : four345Atom p) (t : ℕ) (q : Point3)
    (he : aperyWeight (3*(m+1)) (4*(m+1)) (5*(m+1)) p=
      t*m+aperyWeight (3*(m+1)) (4*(m+1)) (5*(m+1)) q) :
    t=0 ∧ q=p := by
  apply glued_small_unique m 3 4 5 p ?_ ?_ t q he
  · rcases hp with rfl | rfl | rfl <;> simp [aperyWeight] <;> omega
  · intro r hr
    rcases hp with rfl | rfl | rfl
    all_goals dsimp [aperyWeight] at hr
    all_goals apply Point3.ext <;> dsimp <;> omega

def four345Vector (m : ℕ) (i : Fin 4) : FourCoeff :=
  ![pointFour ⟨0,2,0⟩,pointFour ⟨0,1,1⟩,pointFour ⟨0,0,2⟩,
    pureMultiplicity m] i

def four345Isolated (m : ℕ) : Finset FourCoeff := univ.image (four345Vector m)

theorem four345Vector_injective (m : ℕ) : Function.Injective (four345Vector m) := by
  intro i j he
  have h0 := congrFun he (0 : Fin 4)
  have h2 := congrFun he (2 : Fin 4)
  fin_cases i <;> fin_cases j <;>
    simp [four345Vector,pointFour,pureMultiplicity] at h0 h2 ⊢ <;> omega

theorem four345Isolated_card (m : ℕ) : (four345Isolated m).card=4 := by
  rw [four345Isolated,card_image_of_injective _ (four345Vector_injective m)]
  simp

theorem pointFour_positive_x_not_mem_four345 (m : ℕ) (p : Point3) (hp : 0 < p.x) :
    pointFour p∉four345Isolated m := by
  intro h
  obtain ⟨i,_,hi⟩ := mem_image.mp h
  have h0 := congrFun hi (0 : Fin 4)
  have h1 := congrFun hi (1 : Fin 4)
  fin_cases i <;> simp [four345Vector,pointFour,pureMultiplicity] at h0 h1 <;> omega

theorem four345Vector_isolated (m : ℕ) (hm : 6 ≤ m) (i : Fin 4) (v : FourCoeff)
    (he : BaseEdge ![m,3*(m+1),4*(m+1),5*(m+1)]
      (degree ![m,3*(m+1),4*(m+1),5*(m+1)] (four345Vector m i))
      (four345Vector m i) v) : v=four345Vector m i := by
  have hu := four345_atom_unique m hm
  fin_cases i
  · apply pointFour_base_isolated m (3*(m+1)) (4*(m+1)) (5*(m+1))
      four345Atom hu ⟨0,2,0⟩ ?_ ?_ ?_ v he
    all_goals simp [four345Atom,Point3.pred1,Point3.pred2,Point3.pred3]
  · apply pointFour_base_isolated m (3*(m+1)) (4*(m+1)) (5*(m+1))
      four345Atom hu ⟨0,1,1⟩ ?_ ?_ ?_ v he
    all_goals simp [four345Atom,Point3.pred1,Point3.pred2,Point3.pred3]
  · apply pointFour_base_isolated m (3*(m+1)) (4*(m+1)) (5*(m+1))
      four345Atom hu ⟨0,0,2⟩ ?_ ?_ ?_ v he
    all_goals simp [four345Atom,Point3.pred1,Point3.pred2,Point3.pred3]
  · exact pureMultiplicity_isolated m 3 4 5 (by omega) (by omega) (by omega) (by omega) v he

/-- A positive-x representation keeps the gluing witness outside all four isolates. -/
theorem three_four_five_positive_x (m : ℕ) (hm : 6 ≤ m) :
    ∃ p : Point3,0 < p.x ∧ m=3*p.x+4*p.y+5*p.z := by
  by_cases hm9 : 9 ≤ m
  · obtain ⟨x,y,z,hxyz⟩ := three_four_five_representation (m-3) (by omega)
    exact ⟨⟨x+1,y,z⟩,by simp,by dsimp; omega⟩
  · interval_cases m
    · exact ⟨⟨2,0,0⟩,by decide,by decide⟩
    · exact ⟨⟨1,1,0⟩,by decide,by decide⟩
    · exact ⟨⟨1,0,1⟩,by decide,by decide⟩

/-- Four actual isolated factorizations, each with an alternate outside the set. -/
theorem four345_witnesses (m : ℕ) (hm : 6 ≤ m) :
    ∀ u∈four345Isolated m,∃ v,
      degree ![m,3*(m+1),4*(m+1),5*(m+1)] u=
        degree ![m,3*(m+1),4*(m+1),5*(m+1)] v ∧
      v∉four345Isolated m := by
  obtain ⟨p,hpx,hp⟩ := three_four_five_positive_x m hm
  intro u hu
  obtain ⟨i,_,rfl⟩ := mem_image.mp hu
  fin_cases i
  · refine ⟨pointFour ⟨1,0,1⟩,?_,pointFour_positive_x_not_mem_four345 m _ (by decide)⟩
    simp [four345Vector,degree_pointFour,aperyWeight]
    ring
  · refine ⟨pointFour ⟨3,0,0⟩,?_,pointFour_positive_x_not_mem_four345 m _ (by decide)⟩
    simp [four345Vector,degree_pointFour,aperyWeight]
    ring
  · refine ⟨pointFour ⟨2,1,0⟩,?_,pointFour_positive_x_not_mem_four345 m _ (by decide)⟩
    simp [four345Vector,degree_pointFour,aperyWeight]
    ring
  · refine ⟨pointFour p,?_,pointFour_positive_x_not_mem_four345 m p hpx⟩
    simp [four345Vector,pureMultiplicity,degree_four_parts,aperyWeight,pointFour]
    rw [hp]
    ring

/-- Cardinality four is attained by one family at every multiplicity m≥6. -/
theorem rho_four345_ge_four_all (m : ℕ) (hm : 6 ≤ m) :
    4 ≤ intrinsicRho (generatedSemigroup m (3*(m+1)) (4*(m+1)) (5*(m+1))) := by
  have hclass := four_family_minimalFour345 m hm
  have hl := multi_isolated_intrinsic_lower m (3*(m+1)) (4*(m+1)) (5*(m+1))
    hclass (four345Isolated m) (four345_witnesses m hm) (by
      intro u hu v he
      obtain ⟨i,_,rfl⟩ := mem_image.mp hu
      exact four345Vector_isolated m hm i v he)
  rw [four345Isolated_card] at hl
  exact hl

end NSP3.V03
