import NSP3.V03.SpectrumFiveRegion

namespace NSP3.V03

open NSP3.Sharpness NSP3.CommonCard

theorem five_pred_weight_bound (r : ℕ) {p : Point3} (hp : FivePredRegion r p) :
    aperyWeight (fiveA r) (fiveB r) (fiveC r) p <
      aperyWeight (fiveA r) (fiveB r) (fiveC r) ⟨r+1,0,0⟩ := by
  have hA : 0<fiveA r := by rw [fiveA_eq]; omega
  have hB : 0<fiveB r := by unfold fiveB; omega
  have hC : 0<fiveC r := by unfold fiveC; omega
  rcases hp with ⟨hy,hz,hx⟩ | rfl | rfl
  · simp only [aperyWeight,hy,hz,mul_zero,add_zero]
    exact Nat.mul_lt_mul_of_pos_left (by omega) hA
  · have he := (five_border_reductions r).1
    simp only [aperyWeight,mul_zero,mul_one,zero_add,add_zero] at he ⊢
    omega
  · have he := (five_border_reductions r).1
    simp only [aperyWeight,mul_zero,mul_one,zero_add,add_zero] at he ⊢
    omega

/-- Only the proper border predecessors have unique full factorizations;
the remaining Apéry point has the deliberate pure-axis/yz tie. -/
theorem five_pred_unique (r : ℕ) {p : Point3} (hp : FivePredRegion r p)
    (t : ℕ) (q : Point3)
    (he : aperyWeight (fiveA r) (fiveB r) (fiveC r) p =
      t*(r+4)+aperyWeight (fiveA r) (fiveB r) (fiveC r) q) : t=0 ∧ q=p := by
  have hpc := (five_canonical_iff r p).mpr (five_pred_region r hp)
  have hcast : ((t*(r+4)+aperyWeight (fiveA r) (fiveB r) (fiveC r) q : ℕ) :
      ZMod (r+4)) = (aperyWeight (fiveA r) (fiveB r) (fiveC r) q : ZMod (r+4)) := by
    rw [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,mul_zero,zero_add]
  have heZ := (congrArg (fun n : ℕ => (n : ZMod (r+4))) he).trans hcast
  have hres : residueOf (fiveA r : ZMod (r+4)) (fiveB r : ZMod (r+4))
      (fiveC r : ZMod (r+4)) q =
      residueOf (fiveA r : ZMod (r+4)) (fiveB r : ZMod (r+4))
      (fiveC r : ZMod (r+4)) p := by
    rw [← aperyWeight_cast,← aperyWeight_cast]
    exact heZ.symm
  have hmin := aperyCanonical_weight_min _ _ _ _ hpc hres
  have ht : t=0 := by nlinarith
  have hew : aperyWeight (fiveA r) (fiveB r) (fiveC r) q =
      aperyWeight (fiveA r) (fiveB r) (fiveC r) p := by simpa [ht] using he.symm
  have hqmin : WeightMinimal (r+4) (fiveA r) (fiveB r) (fiveC r) q := by
    intro u hu
    have hh := aperyCanonical_weight_min _ _ _ _ hpc (hu.trans hres)
    omega
  have hq : FiveRegion r q := by
    by_contra hn
    obtain ⟨b,hb,hbq⟩ := five_outside_dominates r q hn
    by_cases hbp : b=⟨r+1,0,0⟩
    · subst b
      have hl := Nat.mul_le_mul_left (fiveA r) hbq.1
      have hw : aperyWeight (fiveA r) (fiveB r) (fiveC r) ⟨r+1,0,0⟩ ≤
          aperyWeight (fiveA r) (fiveB r) (fiveC r) q := by
        simp only [aperyWeight,mul_zero,add_zero]
        nlinarith [Nat.zero_le (fiveB r*q.y),Nat.zero_le (fiveC r*q.z)]
      have hpw := five_pred_weight_bound r hp
      exact (not_lt_of_ge (hw.trans_eq hew)) hpw
    · exact five_nonpure_border_not_minimal r b hb hbp
        (weightMinimal_downward _ _ _ _ hbq hqmin)
  exact ⟨ht,five_residue_injective r hq (five_pred_region r hp) hres⟩

private theorem five_atom_of_one (m a b c n : ℕ)
    (hn : n ∈ generatedSemigroup m a b c) (hp : 0<n)
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

theorem five_family_minimalFour (r : ℕ) (hr : 1≤r) :
    MinimalFourGeneratorClass (r+4) (fiveA r) (fiveB r) (fiveC r) := by
  have hA : r+4<fiveA r := by rw [fiveA_eq]; omega
  have hB : r+4<fiveB r := by unfold fiveB; nlinarith
  have hC : r+4<fiveC r := by unfold fiveC; nlinarith
  have hBC : fiveB r<fiveC r := by unfold fiveB fiveC; nlinarith
  have hAC : fiveA r<fiveC r := by
    rw [fiveA_eq]; unfold fiveC
    have : 1≤r*r := Nat.mul_le_mul hr hr
    nlinarith
  have hAB : fiveA r≠fiveB r := by
    by_cases he : r=1
    · subst r; norm_num [fiveA,fiveB]
    · have hr2 : 2≤r := by omega
      rw [fiveA_eq]; unfold fiveB
      nlinarith
  have hmone : ∀ t x y z : ℕ, r+4=t*(r+4)+fiveA r*x+fiveB r*y+fiveC r*z →
      t+x+y+z=1 := by
    intro t x y z he
    have hx : x=0 := by nlinarith [Nat.zero_le (t*(r+4)),Nat.zero_le (fiveB r*y),Nat.zero_le (fiveC r*z)]
    have hy : y=0 := by nlinarith [Nat.zero_le (t*(r+4)),Nat.zero_le (fiveA r*x),Nat.zero_le (fiveC r*z)]
    have hz : z=0 := by nlinarith [Nat.zero_le (t*(r+4)),Nat.zero_le (fiveA r*x),Nat.zero_le (fiveB r*y)]
    subst x; subst y; subst z
    simp only [mul_zero,add_zero] at he
    nlinarith
  have hunit : ∀ p : Point3, (p=⟨1,0,0⟩ ∨ p=⟨0,1,0⟩ ∨ p=⟨0,0,1⟩) →
      ∀ t x y z : ℕ, aperyWeight (fiveA r) (fiveB r) (fiveC r) p =
        t*(r+4)+fiveA r*x+fiveB r*y+fiveC r*z → t+x+y+z=1 := by
    intro p hp t x y z he
    have hsmall : FivePredRegion r p := by
      rcases hp with rfl | rfl | rfl
      · exact Or.inl ⟨rfl,rfl,hr⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have he' : aperyWeight (fiveA r) (fiveB r) (fiveC r) p =
        t*(r+4)+aperyWeight (fiveA r) (fiveB r) (fiveC r) ⟨x,y,z⟩ := by
      simpa [aperyWeight,add_assoc] using he
    obtain ⟨ht,hq⟩ := five_pred_unique r hsmall t ⟨x,y,z⟩ he'
    rcases hp with rfl | rfl | rfl <;>
      have hx := congrArg Point3.x hq <;> have hy := congrArg Point3.y hq <;>
      have hz := congrArg Point3.z hq <;> dsimp at hx hy hz <;> omega
  have hg := generatedSemigroup_generators (r+4) (fiveA r) (fiveB r) (fiveC r)
  refine ⟨?_,by omega,by omega,by omega,by omega,five_gcd r,?_⟩
  · simp [Nat.ne_of_lt hA,Nat.ne_of_lt hB,Nat.ne_of_lt hC,hAB,
      Nat.ne_of_lt hAC,Nat.ne_of_lt hBC]
  · intro n hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · exact five_atom_of_one _ _ _ _ _ hg.1 (by omega) hmone
    · apply five_atom_of_one _ _ _ _ _ hg.2.1 (by omega)
      simpa [aperyWeight] using hunit ⟨1,0,0⟩ (by simp)
    · apply five_atom_of_one _ _ _ _ _ hg.2.2.1 (by omega)
      simpa [aperyWeight] using hunit ⟨0,1,0⟩ (by simp)
    · apply five_atom_of_one _ _ _ _ _ hg.2.2.2 (by omega)
      simpa [aperyWeight] using hunit ⟨0,0,1⟩ (by simp)

theorem five_family_border_cover (r : ℕ) (hr : 1≤r) :
    ∀ p, MinimalComplement (aperyStandardSet (r+4) (fiveA r) (fiveB r) (fiveC r)
      (by omega) (five_gcd r)) p → p ∈ fiveBorder r := by
  intro p hp
  have hmem : ∀ q, q ∈ aperyStandardSet (r+4) (fiveA r) (fiveB r) (fiveC r)
      (by omega) (five_gcd r) ↔ FiveRegion r q := by
    intro q
    exact (mem_aperyStandardSet _ _ _ _ _ _ q).trans (five_canonical_iff r q)
  have hout : ¬ FiveRegion r p := fun hh => hp.not_mem ((hmem p).mpr hh)
  obtain ⟨b,hb,hbp⟩ := five_outside_dominates r p hout
  have hbmin : MinimalComplement (aperyStandardSet (r+4) (fiveA r) (fiveB r) (fiveC r)
      (by omega) (five_gcd r)) b := by
    obtain ⟨hx,hy,hz⟩ := five_border_predecessors r hr b hb
    refine ⟨?_,fun hh => (hmem b.pred1).mpr (five_pred_region r (hx hh)),
      fun hh => (hmem b.pred2).mpr (five_pred_region r (hy hh)),
      fun hh => (hmem b.pred3).mpr (five_pred_region r (hz hh))⟩
    intro hm
    exact five_border_not_canonical r b hb ((mem_aperyStandardSet _ _ _ _ _ _ b).mp hm)
  have he : b=p := by
    by_contra hne
    exact minimalComplement_not_le_of_ne (aperyStandardSet_downset _ _ _ _ _ _) hbmin hp hne hbp
  exact he ▸ hb

theorem five_border_weight_injective (r : ℕ) (hr : 1≤r) :
    Set.InjOn (aperyWeight (fiveA r) (fiveB r) (fiveC r)) (fiveBorder r : Set Point3) := by
  intro p hp q hq he
  simp only [Finset.mem_coe,fiveBorder,Finset.mem_insert,Finset.mem_singleton] at hp hq
  by_cases hr1 : r=1
  · subst r
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | norm_num [aperyWeight,fiveA,fiveB,fiveC] at he
  · have hr2 : 2≤r := by omega
    have hs : 4≤r*r := Nat.mul_le_mul hr2 hr2
    have h₁ : fiveA r+fiveB r<fiveA r+fiveC r := by unfold fiveB fiveC; nlinarith
    have h₂ : fiveA r+fiveC r<2*fiveB r := by rw [fiveA_eq]; unfold fiveB fiveC; nlinarith
    have h₃ : 2*fiveB r<fiveA r*(r+1) := by rw [fiveA_eq]; unfold fiveB; nlinarith
    have h₄ : fiveA r*(r+1)<2*fiveC r := by rw [fiveA_eq]; unfold fiveC; nlinarith
    rcases hp with rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> try rfl
    all_goals simp only [aperyWeight,mul_zero,mul_one,add_zero,zero_add] at he
    all_goals nlinarith

theorem five_family_rho_eq (r : ℕ) (hr : 1≤r) :
    intrinsicRho (generatedSemigroup (r+4) (fiveA r) (fiveB r) (fiveC r))=5 := by
  classical
  have hclass := five_family_minimalFour r hr
  apply le_antisymm
  · have hh := intrinsicRho_le_border_cover _ _ _ _ hclass (fiveBorder r)
      (five_family_border_cover r hr)
    simpa only [five_border_card] using hh
  · let U := (fiveBorder r).image pointFour
    have hcard : U.card=5 := by
      rw [Finset.card_image_of_injective _ pointFour_injective]
      exact five_border_card r
    rw [← hcard]
    apply isolated_degrees_intrinsic_lower _ _ _ _ hclass U
    · intro u hu v hv he
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hv
      rw [degree_pointFour,degree_pointFour] at he
      exact congrArg pointFour (five_border_weight_injective r hr hp hq he)
    · intro u hu
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨h₀,h₁,h₂,h₃,h₄⟩ := five_border_reductions r
      simp only [fiveBorder,Finset.mem_insert,Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl
      · refine ⟨![0,0,1,1],?_,?_⟩
        · rw [degree_pointFour,degree_four_parts]
          simpa [aperyWeight] using h₀
        · intro hh
          have := congrFun hh (1 : Fin 4)
          simp [pointFour] at this
      · refine ⟨![3,0,0,1],?_,?_⟩
        · simpa [degree_pointFour,degree_four_parts,aperyWeight,pointFour,add_comm] using h₁
        · intro hh
          have := congrFun hh (0 : Fin 4)
          norm_num [pointFour] at this
      · refine ⟨![2*r+6,0,0,0],?_,?_⟩
        · simpa [degree_pointFour,degree_four_parts,aperyWeight,pointFour] using h₂
        · intro hh
          have := congrFun hh (0 : Fin 4)
          simp [pointFour] at this
      · refine ⟨![3,r,0,0],?_,?_⟩
        · simpa [degree_pointFour,degree_four_parts,aperyWeight,pointFour,add_comm] using h₃
        · intro hh
          have := congrFun hh (0 : Fin 4)
          norm_num [pointFour] at this
      · refine ⟨![2*r+3,0,1,0],?_,?_⟩
        · simpa [degree_pointFour,degree_four_parts,aperyWeight,pointFour,add_comm] using h₄
        · intro hh
          have := congrFun hh (0 : Fin 4)
          simp [pointFour] at this
    · intro u hu v hb
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨hx,hy,hz⟩ := five_border_predecessors r hr p hp
      exact pointFour_base_isolated _ _ _ _ (FivePredRegion r)
        (fun q hq t w he => five_pred_unique r hq t w he) p hx hy hz v hb

theorem spectrum_five_exists (m : ℕ) (hm : 5 ≤ m) : 5 ∈ sharpRhoValues m := by
  let r := m-4
  have hr : 1≤r := by dsimp [r]; omega
  have he : r+4=m := by dsimp [r]; omega
  have hclass := five_family_minimalFour r hr
  have hs := minimal_generator_class_bridge _ _ _ _ hclass
  rw [← he]
  exact ⟨generatedAddSubmonoid (r+4) (fiveA r) (fiveB r) (fiveC r),
    hs.2.2.2,hs.2.2.1,hs.1,five_family_rho_eq r hr⟩

end NSP3.V03
