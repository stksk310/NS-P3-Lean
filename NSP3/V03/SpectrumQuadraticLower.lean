import NSP3.V03.MultiIsolated
import NSP3.V03.SpectrumQuadraticAtoms

namespace NSP3.V03

open NSP3.Sharpness NSP3.CommonCard

def quadraticPoints : Finset Point3 :=
  {⟨2,0,0⟩,⟨1,1,0⟩,⟨1,0,1⟩,⟨0,2,0⟩,⟨0,1,1⟩,⟨0,0,2⟩}

private def lowPoints : Finset Point3 :=
  {⟨0,0,0⟩,Point3.e1,Point3.e2,Point3.e3}

theorem quadraticPoints_card : quadraticPoints.card=6 := by decide
private theorem lowPoints_card : lowPoints.card=4 := by decide

private theorem lowPoints_disjoint_quadratic : Disjoint lowPoints quadraticPoints := by decide

/-- Each positive-coordinate predecessor of a quadratic vector is a one-term vector. -/
theorem quadratic_predecessor_single (p : Point3) (hp : p∈quadraticPoints)
    (i : Fin 4) (hi : 0<pointFour p i) :
    ∃ j : Fin 4, pointFour p-Pi.single i 1=Pi.single j 1 := by
  simp only [quadraticPoints,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals fin_cases i <;> norm_num [pointFour] at hi
  all_goals decide

private def unitPoint (j : Fin 3) : Point3 := ![Point3.e1,Point3.e2,Point3.e3] j

private theorem pointFour_unitPoint (j : Fin 3) :
    pointFour (unitPoint j)=Pi.single j.succ 1 := by
  fin_cases j <;> funext i <;> fin_cases i <;>
    simp [unitPoint,pointFour,Point3.e1,Point3.e2,Point3.e3,Pi.single_apply]

private theorem unitPoint_weight (m a b c : ℕ) (j : Fin 3) :
    aperyWeight a b c (unitPoint j)=![m,a,b,c] j.succ := by
  fin_cases j <;> simp [unitPoint,aperyWeight,Point3.e1,Point3.e2,Point3.e3]

private theorem input_atom_apery (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (j : Fin 4) (hj : j≠0) :
    ![m,a,b,c] j∈generatedApery m a b c := by
  have hn : SemigroupAtom (generatedSemigroup m a b c) (![m,a,b,c] j) :=
    h.atoms _ (by fin_cases j <;> simp)
  have hne : ![m,a,b,c] j≠m := by
    intro he
    apply hj
    exact input_weights_injective m a b c h (by simpa using he)
  refine ⟨hn.1,?_⟩
  by_cases hs : ![m,a,b,c] j < m
  · exact Or.inl hs
  · apply Or.inr
    intro hp
    have hg := (generatedSemigroup_generators m a b c).1
    have he : ![m,a,b,c] j=m+(![m,a,b,c] j-m) := by omega
    rcases hn.2.2 m hg _ hp he with hz | hz
    · have := h.positive
      omega
    · apply hne
      omega

private theorem unitPoint_mem_canonical (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (j : Fin 3) :
    unitPoint j∈aperyStandardSet m a b c h.positive h.coprime := by
  have hAp : aperyWeight a b c (unitPoint j)∈generatedApery m a b c := by
    rw [unitPoint_weight]
    exact input_atom_apery m a b c h j.succ (by simp)
  rw [generatedApery_eq_weights m a b c h.positive h.coprime] at hAp
  obtain ⟨q,hq,he⟩ := hAp
  have hdegree : degree ![m,a,b,c] (Pi.single j.succ 1)=
      degree ![m,a,b,c] (pointFour q) := by
    simpa [degree_single,degree_pointFour,unitPoint_weight m a b c j] using he
  have hv := input_atom_unique m a b c h j.succ (pointFour q) hdegree
  have hqu : q=unitPoint j := pointFour_injective (hv.trans (pointFour_unitPoint j).symm)
  simpa [hqu] using hq

private theorem lowPoints_subset_canonical (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    lowPoints⊆aperyStandardSet m a b c h.positive h.coprime := by
  have hDn : (aperyStandardSet m a b c h.positive h.coprime).Nonempty := by
    apply Finset.card_pos.mp
    rw [aperyStandardSet_card]
    exact h.positive
  obtain ⟨q,hq⟩ := hDn
  have hzero : (⟨0,0,0⟩ : Point3)∈aperyStandardSet m a b c h.positive h.coprime := by
    apply (aperyStandardSet_downset m a b c h.positive h.coprime) ?_ hq
    change 0≤q.x ∧ 0≤q.y ∧ 0≤q.z
    exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
  intro p hp
  simp only [lowPoints,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact hzero
  · simpa [unitPoint] using unitPoint_mem_canonical m a b c h 0
  · simpa [unitPoint] using unitPoint_mem_canonical m a b c h 1
  · simpa [unitPoint] using unitPoint_mem_canonical m a b c h 2

noncomputable def quadraticVectors (D : Finset Point3) : Finset FourCoeff := by
  classical
  exact (quadraticPoints \ D).image pointFour

/-- Actual all-class quadratic lower bound, including repeated relation degrees. -/
theorem intrinsicRho_add_m_ge_ten (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    10 ≤ m+intrinsicRho (generatedSemigroup m a b c) := by
  classical
  let D := aperyStandardSet m a b c h.positive h.coprime
  have hU : (quadraticVectors D).card ≤ intrinsicRho (generatedSemigroup m a b c) := by
    apply multi_isolated_intrinsic_lower m a b c h (quadraticVectors D)
    · intro u hu
      change u∈(quadraticPoints \ D).image pointFour at hu
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨r,hr,t,he⟩ :=
        (generatedSemigroup_normal_form m a b c h.positive h.coprime
          (aperyWeight a b c p)).mp (aperyWeight_mem_generatedSemigroup m a b c p)
      let v : FourCoeff := ![t,r.x,r.y,r.z]
      refine ⟨v,?_,?_⟩
      · rw [degree_pointFour,degree_four_parts]
        change aperyWeight a b c p=t*m+aperyWeight a b c r
        omega
      · intro hv
        change v∈(quadraticPoints \ D).image pointFour at hv
        obtain ⟨q,hq,hqv⟩ := Finset.mem_image.mp hv
        have ht : t=0 := by
          have hh := congrFun hqv 0
          simpa [v,pointFour] using hh.symm
        have hqr : q=r := by
          apply pointFour_injective
          simpa [v,pointFour,ht] using hqv
        apply (Finset.mem_sdiff.mp hq).2
        simpa [hqr] using hr
    · intro u hu v hb
      change u∈(quadraticPoints \ D).image pointFour at hu
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
      apply base_isolated_of_unique_predecessors ![m,a,b,c] (pointFour p) ?_ v hb
      intro i hi w he
      obtain ⟨j,hpred⟩ :=
        quadratic_predecessor_single p (Finset.mem_sdiff.mp hp).1 i hi
      rw [hpred] at he ⊢
      exact input_atom_unique m a b c h j w he
  have hcardU : (quadraticVectors D).card=(quadraticPoints \ D).card := by
    unfold quadraticVectors
    exact Finset.card_image_of_injective _ pointFour_injective
  have hpartition := Finset.card_sdiff_add_card_inter quadraticPoints D
  have hdisj : Disjoint lowPoints (quadraticPoints ∩ D) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.disjoint_left.mp lowPoints_disjoint_quadratic) hp
      (Finset.mem_inter.mp hq).1
  have hsub : lowPoints ∪ (quadraticPoints ∩ D)⊆D := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact lowPoints_subset_canonical m a b c h hp
    · exact (Finset.mem_inter.mp hp).2
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,lowPoints_card] at hcount
  have hDcard : D.card=m := aperyStandardSet_card m a b c h.positive h.coprime
  rw [hDcard] at hcount
  rw [quadraticPoints_card] at hpartition
  rw [hcardU] at hU
  omega

/-- The same lower bound transported to the whole original numerical-semigroup class. -/
theorem spectrum_member_add_m_ge_ten {m q : ℕ} (hq : q∈sharpRhoValues m) :
    10 ≤ m+q := by
  rcases hq with ⟨S,hcof,hedim,hmult,hrho⟩
  obtain ⟨a,b,c,h,heq⟩ := numerical_semigroup_class_coverage S m hcof hedim hmult
  have hset : generatedSemigroup m a b c=(S : Set ℕ) :=
    congrArg (fun T : AddSubmonoid ℕ => (T : Set ℕ)) heq
  rw [← hrho]
  simpa only [hset] using intrinsicRho_add_m_ge_ten m a b c h

theorem spectrum_four_multiplicity {m : ℕ} (hq : 4∈sharpRhoValues m) : 6 ≤ m := by
  have hh := spectrum_member_add_m_ge_ten hq
  omega

theorem spectrum_five_multiplicity {m : ℕ} (hq : 5∈sharpRhoValues m) : 5 ≤ m := by
  have hh := spectrum_member_add_m_ge_ten hq
  omega

end NSP3.V03
