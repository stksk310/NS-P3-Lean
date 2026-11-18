import NSP3.V03.SpectrumQuadraticAtoms
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
A degree-three truncation argument in twenty dimensions.  The numerical
presentation is genuine; no complete-intersection or Hilbert-series premise
is assumed.  Three relations have at most twelve surviving contexts, while
the canonical Apéry representatives supply at most m further generators.
-/
namespace NSP3.V03
open NSP3.CommonCard NSP3.Sharpness Finset

set_option maxHeartbeats 8000000

def cubicPoints : Finset Point3 :=
  (((range 4).product ((range 4).product (range 4))).image
    (fun q => Point3.mk q.1 q.2.1 q.2.2)).filter (fun p => p.x+p.y+p.z ≤ 3)

@[simp] theorem mem_cubicPoints (p : Point3) :
    p∈cubicPoints ↔ p.x+p.y+p.z ≤ 3 := by
  constructor
  · exact fun h => (mem_filter.mp h).2
  · intro h
    apply mem_filter.mpr
    refine ⟨mem_image.mpr ⟨(p.x,(p.y,p.z)),?_,rfl⟩,h⟩
    exact mem_product.mpr ⟨mem_range.mpr (by change p.x < 4; omega),
      mem_product.mpr ⟨mem_range.mpr (by change p.y < 4; omega),
        mem_range.mpr (by change p.z < 4; omega)⟩⟩

theorem cubicPoints_card : cubicPoints.card=20 := by decide

abbrev CubicMonomial := {p : Point3 // p∈cubicPoints}
abbrev CubicSpace := CubicMonomial→ℚ

theorem cubicMonomial_card : Fintype.card CubicMonomial=20 := by
  simpa using cubicPoints_card

theorem cubicSpace_finrank : Module.finrank ℚ CubicSpace=20 := by
  simp [CubicSpace,cubicPoints_card]

def cubicTail (u : FourCoeff) : Point3 := ⟨u 1,u 2,u 3⟩
def cubicProj (u : FourCoeff) : CubicSpace :=
  fun p => if u 0=0 ∧ cubicTail u=p.val then 1 else 0

theorem cubicProj_zero_m {u : FourCoeff} (hu : u 0≠0) : cubicProj u=0 := by
  funext p
  simp [cubicProj,hu]

theorem cubicProj_zero_high {u : FourCoeff} (hu : 4 ≤ u 1+u 2+u 3) :
    cubicProj u=0 := by
  funext p
  have hp := (mem_cubicPoints p.val).mp p.property
  have hn : cubicTail u≠p.val := by
    intro he
    have hx := congrArg Point3.x he
    have hy := congrArg Point3.y he
    have hz := congrArg Point3.z he
    dsimp [cubicTail] at hx hy hz
    omega
  simp [cubicProj,hn]

theorem cubicProj_point (p : CubicMonomial) :
    cubicProj (pointFour p.val)=Pi.single p (1 : ℚ) := by
  classical
  funext q
  change (if 0=0 ∧ p.val=q.val then (1 : ℚ) else 0)=
    (Pi.single p (1 : ℚ) : CubicSpace) q
  by_cases he : p=q
  · subst q; simp
  · have hv : p.val≠q.val := fun h => he (Subtype.ext h)
    simp [he,hv,Pi.single_apply]

def fourLength (u : FourCoeff) : ℕ := u 0+u 1+u 2+u 3

private theorem length_le_one_cases (u : FourCoeff) (hu : fourLength u ≤ 1) :
    u=0 ∨ ∃ j : Fin 4,u=Pi.single j 1 := by
  have hh :
      (u 0=0 ∧ u 1=0 ∧ u 2=0 ∧ u 3=0) ∨
      (u 0=1 ∧ u 1=0 ∧ u 2=0 ∧ u 3=0) ∨
      (u 0=0 ∧ u 1=1 ∧ u 2=0 ∧ u 3=0) ∨
      (u 0=0 ∧ u 1=0 ∧ u 2=1 ∧ u 3=0) ∨
      (u 0=0 ∧ u 1=0 ∧ u 2=0 ∧ u 3=1) := by unfold fourLength at hu; omega
  rcases hh with hh | hh | hh | hh | hh
  · left; funext j; fin_cases j <;> simp_all
  · right; refine ⟨0,?_⟩; funext j; fin_cases j <;> simp_all [Pi.single_apply]
  · right; refine ⟨1,?_⟩; funext j; fin_cases j <;> simp_all [Pi.single_apply]
  · right; refine ⟨2,?_⟩; funext j; fin_cases j <;> simp_all [Pi.single_apply]
  · right; refine ⟨3,?_⟩; funext j; fin_cases j <;> simp_all [Pi.single_apply]

theorem relation_endpoint_length (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (u v : FourCoeff) (he : degree ![m,a,b,c] u=degree ![m,a,b,c] v)
    (hne : u≠v) : 2 ≤ fourLength u := by
  by_contra hn
  have hs : fourLength u ≤ 1 := by omega
  rcases length_le_one_cases u hs with rfl | ⟨j,rfl⟩
  · have hg : ∀ i : Fin 4,0 < ![m,a,b,c] i := by
      have hm := h.positive
      have ha := h.least_a
      have hb := h.least_b
      have hc := h.least_c
      intro i
      fin_cases i <;> simp <;> omega
    have hv : v=0 := (degree_eq_zero_iff _ hg v).mp (by simpa using he.symm)
    exact hne hv.symm
  · exact hne (input_atom_unique m a b c h j v he).symm

def cubicContext (i : Fin 4) : FourCoeff :=
  ![0,Pi.single (1 : Fin 4) 1,Pi.single (2 : Fin 4) 1,Pi.single (3 : Fin 4) 1] i

private theorem small_context (d : FourCoeff) (h0 : d 0=0)
    (ht : d 1+d 2+d 3 ≤ 1) : ∃ i : Fin 4,d=cubicContext i := by
  have hh :
      (d 1=0 ∧ d 2=0 ∧ d 3=0) ∨
      (d 1=1 ∧ d 2=0 ∧ d 3=0) ∨
      (d 1=0 ∧ d 2=1 ∧ d 3=0) ∨
      (d 1=0 ∧ d 2=0 ∧ d 3=1) := by omega
  rcases hh with hh | hh | hh | hh
  · refine ⟨0,?_⟩; funext j; fin_cases j <;> simp_all [cubicContext]
  · refine ⟨1,?_⟩; funext j; fin_cases j <;> simp_all [cubicContext,Pi.single_apply]
  · refine ⟨2,?_⟩; funext j; fin_cases j <;> simp_all [cubicContext,Pi.single_apply]
  · refine ⟨3,?_⟩; funext j; fin_cases j <;> simp_all [cubicContext,Pi.single_apply]

noncomputable def cubicRelations (R : Finset (FourCoeff×FourCoeff)) : Finset CubicSpace := by
  classical
  exact (R.product (univ : Finset (Fin 4))).image
    (fun e => cubicProj (e.1.1+cubicContext e.2)-cubicProj (e.1.2+cubicContext e.2))

noncomputable def cubicRelationSpan (R : Finset (FourCoeff×FourCoeff)) :
    Submodule ℚ CubicSpace := Submodule.span ℚ (cubicRelations R : Set CubicSpace)

theorem cubicRelations_card_le (R : Finset (FourCoeff×FourCoeff)) :
    (cubicRelations R).card ≤ 4*R.card := by
  classical
  have hc := card_image_le (s := R.product (univ : Finset (Fin 4)))
    (f := fun e => cubicProj (e.1.1+cubicContext e.2)-cubicProj (e.1.2+cubicContext e.2))
  simpa [cubicRelations,card_product,Nat.mul_comm] using hc

private theorem high_context_zero (u d : FourCoeff) (hu : 2 ≤ fourLength u)
    (hd : 2 ≤ d 1+d 2+d 3) : cubicProj (u+d)=0 := by
  by_cases h0 : u 0=0
  · apply cubicProj_zero_high
    simp only [Pi.add_apply]
    unfold fourLength at hu
    omega
  · apply cubicProj_zero_m
    simp only [Pi.add_apply]
    omega

theorem raw_context_mem (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (R : Finset (FourCoeff×FourCoeff)) (hR : NumericPresentation (degree ![m,a,b,c]) R)
    {u v : FourCoeff} (he : (u,v)∈R) (d : FourCoeff) :
    cubicProj (u+d)-cubicProj (v+d)∈cubicRelationSpan R := by
  classical
  by_cases huv : u=v
  · subst v; simp
  have hweight := (hR _ _).mp (GeneratedAddRel.edge he)
  have hu := relation_endpoint_length m a b c h u v hweight huv
  have hv := relation_endpoint_length m a b c h v u hweight.symm (Ne.symm huv)
  by_cases hd0 : d 0=0
  · by_cases hdt : d 1+d 2+d 3 ≤ 1
    · obtain ⟨i,rfl⟩ := small_context d hd0 hdt
      apply Submodule.subset_span
      apply mem_image.mpr
      exact ⟨((u,v),i),mem_product.mpr ⟨he,mem_univ _⟩,rfl⟩
    · have hdt' : 2 ≤ d 1+d 2+d 3 := by omega
      rw [high_context_zero u d hu hdt',high_context_zero v d hv hdt',sub_self]
      exact Submodule.zero_mem _
  · have hu0 : cubicProj (u+d)=0 := cubicProj_zero_m (by simp only [Pi.add_apply]; omega)
    have hv0 : cubicProj (v+d)=0 := cubicProj_zero_m (by simp only [Pi.add_apply]; omega)
    rw [hu0,hv0,sub_self]
    exact Submodule.zero_mem _

/-- All generated paths, including nested contexts, land in the same finite span. -/
theorem generated_cubic_mem (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (R : Finset (FourCoeff×FourCoeff)) (hR : NumericPresentation (degree ![m,a,b,c]) R)
    {u v : FourCoeff} (he : GeneratedAddRel R u v) :
    ∀ d,cubicProj (u+d)-cubicProj (v+d)∈cubicRelationSpan R := by
  induction he with
  | edge he => exact raw_context_mem m a b c h R hR he
  | refl u => intro d; simp
  | symm he ih =>
      intro d
      simpa only [neg_sub] using (cubicRelationSpan R).neg_mem (ih d)
  | trans he₁ he₂ ih₁ ih₂ =>
      intro d
      convert (cubicRelationSpan R).add_mem (ih₁ d) (ih₂ d) using 1 <;> abel
  | context he e ih =>
      intro d
      simpa only [add_assoc] using ih (e+d)

noncomputable def cubicGenerators (D : Finset Point3)
    (R : Finset (FourCoeff×FourCoeff)) : Finset CubicSpace := by
  classical
  exact cubicRelations R ∪ D.image (fun p => cubicProj (pointFour p))

theorem cubicGenerators_card_le (D : Finset Point3) (R : Finset (FourCoeff×FourCoeff)) :
    (cubicGenerators D R).card ≤ 4*R.card+D.card := by
  classical
  have hu := card_union_le (cubicRelations R) (D.image (fun p => cubicProj (pointFour p)))
  have hr := cubicRelations_card_le R
  have hd := card_image_le (s := D) (f := fun p => cubicProj (pointFour p))
  change (cubicGenerators D R).card ≤ _ at hu
  omega

theorem cubicGenerators_span_top (m a b c : ℕ) (h : MinimalFourGeneratorClass m a b c)
    (R : Finset (FourCoeff×FourCoeff)) (hR : NumericPresentation (degree ![m,a,b,c]) R) :
    Submodule.span ℚ (cubicGenerators (aperyStandardSet m a b c h.positive h.coprime) R :
      Set CubicSpace)=⊤ := by
  classical
  let D := aperyStandardSet m a b c h.positive h.coprime
  let K := Submodule.span ℚ (cubicGenerators D R : Set CubicSpace)
  have hsub : cubicRelationSpan R ≤ K := by
    apply Submodule.span_mono
    intro v hv
    exact mem_union_left _ hv
  have hbasis (p : CubicMonomial) : Pi.single p (1 : ℚ)∈K := by
    obtain ⟨q,hq,t,ht⟩ := (generatedSemigroup_normal_form m a b c h.positive h.coprime
      (aperyWeight a b c p.val)).mp (aperyWeight_mem_generatedSemigroup m a b c p.val)
    let v : FourCoeff := ![t,q.x,q.y,q.z]
    have hw : degree ![m,a,b,c] (pointFour p.val)=degree ![m,a,b,c] v := by
      rw [degree_pointFour,degree_four_parts]
      simpa [v,add_comm] using ht
    have hd := generated_cubic_mem m a b c h R hR ((hR _ _).mpr hw) 0
    simp only [add_zero] at hd
    have hdiff := hsub hd
    have hv : cubicProj v∈K := by
      by_cases ht0 : t=0
      · have heq : v=pointFour q := by
          funext i
          fin_cases i <;> simp [v,pointFour,ht0]
        rw [heq]
        apply Submodule.subset_span
        apply mem_union_right
        exact mem_image.mpr ⟨q,hq,rfl⟩
      · rw [cubicProj_zero_m (by simpa [v] using ht0)]
        exact K.zero_mem
    rw [← cubicProj_point p]
    simpa only [sub_add_cancel] using K.add_mem hdiff hv
  apply Submodule.eq_top_iff'.mpr
  intro v
  refine Pi.single_induction (fun w : CubicSpace => w∈K) v K.zero_mem
    (fun _ _ hf hg => K.add_mem hf hg) ?_
  intro p a
  have hs : a • (Pi.single p (1 : ℚ) : CubicSpace)=(Pi.single p a : CubicSpace) := by
    funext q
    by_cases he : q=p
    · subst q; simp
    · simp [Pi.single_apply,he,Ne.symm he]
  rw [← hs]
  exact K.smul_mem a (hbasis p)

theorem numericPresentation_cubic_lower (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c)
    (R : Finset (FourCoeff×FourCoeff)) (hR : NumericPresentation (degree ![m,a,b,c]) R) :
    20 ≤ m+4*R.card := by
  classical
  let D := aperyStandardSet m a b c h.positive h.coprime
  have htop := cubicGenerators_span_top m a b c h R hR
  change Submodule.span ℚ (cubicGenerators D R : Set CubicSpace)=⊤ at htop
  have hdim := finrank_span_finset_le_card (R := ℚ) (cubicGenerators D R)
  change Module.finrank ℚ (Submodule.span ℚ (cubicGenerators D R : Set CubicSpace))≤
    (cubicGenerators D R).card at hdim
  rw [htop] at hdim
  have hdim' : 20 ≤ (cubicGenerators D R).card := by
    simpa [cubicSpace_finrank,cubicPoints_card] using hdim
  have hc := cubicGenerators_card_le D R
  have hD : D.card=m := aperyStandardSet_card m a b c h.positive h.coprime
  omega

/-- A real relation-number bound on the actual four-atom numerical class. -/
theorem intrinsicRho_cubic_lower (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    20 ≤ m+4*intrinsicRho (generatedSemigroup m a b c) := by
  obtain ⟨R,hR,hcard⟩ := intrinsicRho_attained m a b c h
  let e := atomToFour m a b c h
  have ht := (numericPresentation_transport e (atomWeight (generatedSemigroup m a b c))
    (degree ![m,a,b,c]) (atomToFour_weight m a b c h) R).mpr hR
  have hl := numericPresentation_cubic_lower m a b c h (mapRelations e R) ht
  rwa [mapRelations_card,hcard] at hl

theorem rho_three_multiplicity_ge_eight (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c)
    (hrho : intrinsicRho (generatedSemigroup m a b c)=3) : 8 ≤ m := by
  have hl := intrinsicRho_cubic_lower m a b c h
  rw [hrho] at hl
  omega

end NSP3.V03
