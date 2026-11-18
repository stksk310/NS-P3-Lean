import P3TorSpike.BinomialKernel
import P3TorSpike.BinomialFibre

noncomputable section
namespace NSP3.TorSpike

def polynomialAugmentation (k : Type) [Field k] : PolynomialRing k →ₐ[k] k :=
  MvPolynomial.aeval (fun _ : Fin 4 => (0 : k))

abbrev relationKernel (k : Type) [Field k] (m a b c : ℕ) :=
  RingHom.ker (polynomialMap k m a b c).toRingHom

/-- The actual relation space I/(X₀,X₁,X₂,X₃)I. -/
abbrev relationConormal (k : Type) [Field k] (m a b c : ℕ) :=
  augmentationFibre (M := relationKernel k m a b c) (polynomialAugmentation k)

def relationGenerator (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R) (e : R) :
    relationKernel k m a b c :=
  ⟨relationBinomial k e.val, binomialIdeal_le_ker k m a b c R hR
    (Ideal.subset_span ⟨e.val, e.property, rfl⟩)⟩

theorem relationGenerator_span (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R) :
    Submodule.span (PolynomialRing k) (Set.range (relationGenerator k m a b c R hR)) = ⊤ := by
  apply (Submodule.span_range_subtype_eq_top_iff (relationKernel k m a b c)
    (fun e : R => (relationGenerator k m a b c R hR e).property)).mpr
  have hrange : Set.range (fun e : R => relationBinomial k e.val) =
      relationBinomial k '' (R : Set (Fact4 × Fact4)) := by
    ext p
    constructor
    · rintro ⟨e, rfl⟩; exact ⟨e.val, e.property, rfl⟩
    · rintro ⟨e, he, rfl⟩; exact ⟨⟨e, he⟩, rfl⟩
  change Submodule.span (PolynomialRing k) (Set.range (fun e : R => relationBinomial k e.val)) = _
  rw [hrange]
  exact binomialIdeal_eq_ker k m a b c R hR

/-- An explicit finite free-module map surjecting onto the genuine polynomial kernel. -/
def freeRelationMap (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R) :
    (R →₀ PolynomialRing k) →ₗ[PolynomialRing k] relationKernel k m a b c :=
  Finsupp.linearCombination (PolynomialRing k) (relationGenerator k m a b c R hR)

theorem freeRelationMap_surjective (k : Type) [Field k] (m a b c : ℕ)
    (R : Finset (Fact4 × Fact4)) (hR : IsFactorPresentation m a b c R) :
    Function.Surjective (freeRelationMap k m a b c R hR) := by
  apply LinearMap.range_eq_top.mp
  rw [freeRelationMap, Finsupp.range_linearCombination]
  exact relationGenerator_span k m a b c R hR

theorem relationConormal_finite (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) : Module.Finite k (relationConormal k m a b c) := by
  obtain ⟨R, hR, _, _⟩ := minimal_binomial_kernel_presentation k m a b c h
  exact augmentationFibre_finite (polynomialAugmentation k) _ (relationGenerator_span k m a b c R hR)

/-- The true relation space has dimension at most the intrinsic finite relation count.
    Equality requires the separate independence/minimality argument. -/
theorem relationConormal_finrank_le_intrinsicRho (k : Type) [Field k] (m a b c : ℕ)
    (h : MinimalFourGeneratorClass m a b c) :
    Module.finrank k (relationConormal k m a b c) ≤ intrinsicRho (generatedSemigroup m a b c) := by
  obtain ⟨R, hR, hc, _⟩ := minimal_binomial_kernel_presentation k m a b c h
  have hh := augmentationFibre_finrank_le (polynomialAugmentation k) _
    (relationGenerator_span k m a b c R hR)
  simpa only [Fintype.card_coe, hc] using hh

end NSP3.TorSpike
