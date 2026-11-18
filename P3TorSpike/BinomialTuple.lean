import P3TorSpike.BinomialVars

noncomputable section
namespace NSP3.TorSpike

section VariableCombination
variable {k M : Type} [Field k] [AddCommGroup M] [Module (PolynomialRing k) M]
  [Module k M] [IsScalarTower k (PolynomialRing k) M]

/-- The genuine first variable differential on any polynomial module. -/
def variableCombination : (Fin 4 → M) →ₗ[PolynomialRing k] M where
  toFun f := ∑ i, (MvPolynomial.X i : PolynomialRing k) • f i
  map_add' f g := by simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    congr 1
    funext i
    exact smul_comm _ _ _

@[simp] theorem variableCombination_single (i : Fin 4) (x : M) :
    variableCombination (k := k) (Pi.single i x) = (MvPolynomial.X i : PolynomialRing k) • x := by
  classical
  simp [variableCombination, Pi.single_apply, Finset.sum_ite_eq']

theorem augmentationSubmodule_eq_range_variableCombination :
    augmentationSubmodule (M := M) (polynomialAugmentation k) =
      LinearMap.range (variableCombination (k := k) (M := M)) := by
  apply le_antisymm
  · rw [augmentationSubmodule, polynomialAugmentation_ker]
    apply Submodule.smul_le.mpr
    intro r hr x hx
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨i, rfl⟩ := hr
      exact ⟨Pi.single i x, variableCombination_single i x⟩
    | zero => simpa only [zero_smul] using (LinearMap.range (variableCombination (k := k) (M := M))).zero_mem
    | add r s hr hs ihr ihs =>
      simpa only [add_smul] using (LinearMap.range (variableCombination (k := k) (M := M))).add_mem ihr ihs
    | smul p r hr ih =>
      simpa only [smul_eq_mul, mul_smul] using
        (LinearMap.range (variableCombination (k := k) (M := M))).smul_mem p ih
  · rintro x ⟨f, rfl⟩
    change (∑ i, (MvPolynomial.X i : PolynomialRing k) • f i) ∈
      RingHom.ker (polynomialAugmentation k).toRingHom • (⊤ : Submodule (PolynomialRing k) M)
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem_smul
    · change polynomialAugmentation k (MvPolynomial.X i) = 0
      simp [polynomialAugmentation]
    · trivial

theorem mem_augmentationSubmodule_iff_variableCombination (x : M) :
    x ∈ augmentationSubmodule (M := M) (polynomialAugmentation k) ↔
      ∃ f : Fin 4 → M, variableCombination (k := k) f = x := by
  rw [augmentationSubmodule_eq_range_variableCombination]
  rfl

end VariableCombination

/-- A relation lies in mI exactly when it is a sum of the variables times four actual relations. -/
theorem relationKernel_augmentationSubmodule_tuple (k : Type) [Field k] (m a b c : ℕ)
    (x : relationKernel k m a b c) :
    x ∈ augmentationSubmodule (M := relationKernel k m a b c) (polynomialAugmentation k) ↔
      ∃ f : Fin 4 → relationKernel k m a b c,
        ∑ i, (MvPolynomial.X i : PolynomialRing k) * (f i : PolynomialRing k) = (x : PolynomialRing k) := by
  rw [mem_augmentationSubmodule_iff_variableCombination]
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, ?_⟩
    simpa only [variableCombination, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] using congrArg Subtype.val hf
  · rintro ⟨f, hf⟩
    refine ⟨f, Subtype.ext ?_⟩
    simpa only [variableCombination, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.coe_sum, Submodule.coe_smul, smul_eq_mul] using hf

end NSP3.TorSpike
