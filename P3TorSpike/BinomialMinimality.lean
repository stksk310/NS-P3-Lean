import P3TorSpike.BinomialCuts

noncomputable section
namespace NSP3.TorSpike

def kernelCut (k : Type) [Field k] (m a b c : ℕ) (R : Finset (Fact4 × Fact4))
    (e : Fact4 × Fact4) : relationKernel k m a b c →ₗ[k] k :=
  (binomialCut k m a b c R e).comp ((relationKernel k m a b c).subtype.restrictScalars k)

theorem kernelCut_augmentationSubmodule (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R) (e : Fact4 × Fact4)
    (x : relationKernel k m a b c)
    (hx : x ∈ augmentationSubmodule (M := relationKernel k m a b c) (polynomialAugmentation k)) :
    kernelCut k m a b c R e x = 0 := by
  change x ∈ RingHom.ker (polynomialAugmentation k).toRingHom •
    (⊤ : Submodule (PolynomialRing k) (relationKernel k m a b c)) at hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro q hq y hy
    change binomialCut k m a b c R e (q * (y : PolynomialRing k)) = 0
    rw [binomialCut_mul_mem k m a b c h R hR e y.val (by
      rw [binomialIdeal_eq_ker k m a b c R hR]; exact y.property)]
    have hq' : polynomialAugmentation k q = 0 := hq
    rw [hq', zero_mul]
  · intro y z hy hz
    rw [map_add, hy, hz, add_zero]

/-- Every indispensable presentation edge has a field-valued functional on the actual conormal. -/
def relationCut (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R) (e : Fact4 × Fact4) :
    relationConormal k m a b c →ₗ[k] k :=
  ((augmentationSubmodule (M := relationKernel k m a b c) (polynomialAugmentation k)).restrictScalars k).liftQ
    (kernelCut k m a b c R e)
    (fun x hx => kernelCut_augmentationSubmodule k m a b c h R hR e x hx)

def conormalGenerator (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R) (e : R) :
    relationConormal k m a b c := Submodule.Quotient.mk (relationGenerator k m a b c R hR e)

@[simp] theorem relationCut_generator (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R) (e f : R) :
    relationCut k m a b c h R hR e.val (conormalGenerator k m a b c R hR f) =
      binomialCut k m a b c R e.val (relationBinomial k f.val) := rfl

/-- No characteristic-zero argument is used: component cuts separate all minimal relation classes. -/
theorem conormalGenerator_linearIndependent (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R)
    (hmin : ∀ e ∈ R, ¬ GeneratedAddRel (R.erase e) e.1 e.2) :
    LinearIndependent k (conormalGenerator k m a b c R hR) := by
  classical
  rw [linearIndependent_iff_notMem_span]
  intro e hm
  have hz : ∀ x ∈ Submodule.span k (conormalGenerator k m a b c R hR '' (Set.univ \ {e})),
      relationCut k m a b c h R hR e.val x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      rw [relationCut_generator]
      apply binomialCut_other_relation k m a b c R hR e.val f.val f.property
      intro hfe
      exact hf.2 (by simpa using Subtype.ext hfe)
    | zero => exact map_zero _
    | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
    | smul a x hx ih => rw [map_smul, ih, smul_zero]
  have ho : relationCut k m a b c h R hR e.val (conormalGenerator k m a b c R hR e) = 1 := by
    rw [relationCut_generator]
    exact binomialCut_own_relation k m a b c R hR e.val e.property (hmin _ e.property)
  have hc := hz _ hm
  rw [ho] at hc
  exact one_ne_zero hc

theorem conormalGenerator_span (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R) :
    Submodule.span k (Set.range (conormalGenerator k m a b c R hR)) = ⊤ :=
  augmentationFibre_span_eq_top (polynomialAugmentation k) _ (relationGenerator_span k m a b c R hR)

/-- A genuine inclusion-minimal monoid presentation supplies a basis of I/(X₀,X₁,X₂,X₃)I. -/
def conormalBasis (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R)
    (hmin : ∀ e ∈ R, ¬ GeneratedAddRel (R.erase e) e.1 e.2) :
    Module.Basis R k (relationConormal k m a b c) :=
  Module.Basis.mk (conormalGenerator_linearIndependent k m a b c h R hR hmin)
    (by rw [conormalGenerator_span])

theorem minimum_presentation_edge_indispensable (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) (R : Finset (Fact4 × Fact4))
    (hR : IsFactorPresentation m a b c R)
    (hc : R.card = intrinsicRho (generatedSemigroup m a b c)) :
    ∀ e ∈ R, ¬ GeneratedAddRel (R.erase e) e.1 e.2 := by
  classical
  have hRg : CommonCard.NumericPresentation (factorWeight m a b c) R := by
    intro u v
    rw [generatedAddRel_four_iff]
    exact hR u v
  apply CommonCard.minimal_edge_not_generated (factorWeight m a b c) R hRg
  intro T hT hTp
  have hTf : IsFactorPresentation m a b c T := by
    intro u v
    rw [← generatedAddRel_four_iff]
    exact hTp u v
  have hl : intrinsicRho (generatedSemigroup m a b c) ≤ T.card := by
    rw [literature_rho_identification m a b c h]
    exact minimumFourInputRelations_le m a b c T hTf
  have ht := Finset.card_lt_card hT
  omega

/-- The actual conormal dimension equals the intrinsic minimum relation count over every field. -/
theorem relationConormal_finrank_eq_intrinsicRho (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    Module.finrank k (relationConormal k m a b c) = intrinsicRho (generatedSemigroup m a b c) := by
  classical
  obtain ⟨R, hR, hc, _⟩ := minimal_binomial_kernel_presentation k m a b c h
  have hb := conormalBasis k m a b c h R hR (minimum_presentation_edge_indispensable m a b c h R hR hc)
  exact (Module.finrank_eq_card_finset_basis hb).trans hc

end NSP3.TorSpike
