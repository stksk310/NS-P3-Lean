import P3TorSpike.RegularReductionQuotient

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace NSP3.TorSpike.RegularReduction
open CategoryTheory
variable (k R : Type) [Field k] [CommRing R] [Algebra k R]

def multiplyH2 (t : R) (u : Fin 3 → R) : threeH2Complex k R u ⟶ threeH2Complex k R u where
  τ₁ := ModuleCat.ofHom (multiply k R t)
  τ₂ := ModuleCat.ofHom (multiplyPi k R t (Fin 3))
  τ₃ := ModuleCat.ofHom (multiplyPi k R t (Fin 3))
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change threeD3 k R u (multiply k R t v) = multiplyPi k R t (Fin 3) (threeD3 k R u v)
    funext i
    fin_cases i <;> simp [multiplyPi,multiply,threeD3] <;> ring
  comm₂₃ := by
    exact (multiplyH1 k R t u).comm₁₂

def quotientH2 (t : R) (u : Fin 3 → R) :
    threeH2Complex k R u ⟶ threeH2Complex k (QuotientRing R t) (fun i => quotientAlg k R t (u i)) where
  τ₁ := ModuleCat.ofHom (quotientAlg k R t).toLinearMap
  τ₂ := ModuleCat.ofHom (quotientPi k R t (Fin 3))
  τ₃ := ModuleCat.ofHom (quotientPi k R t (Fin 3))
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change threeD3 k (QuotientRing R t) (fun i => quotientAlg k R t (u i))
      (quotientAlg k R t v) = quotientPi k R t (Fin 3) (threeD3 k R u v)
    funext i
    fin_cases i <;> simp [quotientPi,threeD3]
  comm₂₃ := by
    exact (quotientH1 k R t u).comm₁₂

/-- Actual second Koszul cone homology after killing a regular element. -/
def regularH2Equiv (t : R) (u : Fin 3 → R) (ht : Function.Injective (multiply k R t)) :
    (coneShortComplex (threeH2Complex k R u) (multiplyH2 k R t u)
      (threeD1 k R u) (threeD1_comp_threeD2 k R u)).homology ≃ₗ[k]
    (threeH2Complex k (QuotientRing R t) (fun i => quotientAlg k R t (u i))).homology := by
  apply coneQuotientHomologyEquiv (quotientH2 k R t u)
    (threeD1 k R u) (threeD1_comp_threeD2 k R u) (multiply k R t)
  · exact ModuleCat.hom_ext_iff.mp (multiplyH1 k R t u).comm₂₃
  · exact multiplyPi_injective k R t ht (Fin 3)
  · exact ht
  · exact range_multiplyPi_eq_ker_quotientPi k R t (Fin 3)
  · exact range_multiplyPi_eq_ker_quotientPi k R t (Fin 3)
  · exact quotientPi_surjective k R t (Fin 3)
  · exact quotient_surjective k R t

/-- The third homology short complex, with its genuine zero incoming term. -/
def threeH3Complex (u : Fin 3 → R) : ShortComplex (ModuleCat.{0} k) :=
  ShortComplex.moduleCatMk (0 : (Fin 0 → R) →ₗ[k] R) (threeD3 k R u) (by exact LinearMap.comp_zero _)

def multiplyH3 (t : R) (u : Fin 3 → R) : threeH3Complex k R u ⟶ threeH3Complex k R u where
  τ₁ := ModuleCat.ofHom (multiplyPi k R t (Fin 0))
  τ₂ := ModuleCat.ofHom (multiply k R t)
  τ₃ := ModuleCat.ofHom (multiplyPi k R t (Fin 3))
  comm₁₂ := by ext x; simp [threeH3Complex]
  comm₂₃ := (multiplyH2 k R t u).comm₁₂

def quotientH3 (t : R) (u : Fin 3 → R) :
    threeH3Complex k R u ⟶ threeH3Complex k (QuotientRing R t) (fun i => quotientAlg k R t (u i)) where
  τ₁ := ModuleCat.ofHom (quotientPi k R t (Fin 0))
  τ₂ := ModuleCat.ofHom (quotientAlg k R t).toLinearMap
  τ₃ := ModuleCat.ofHom (quotientPi k R t (Fin 3))
  comm₁₂ := by ext x; simp [threeH3Complex]
  comm₂₃ := (quotientH2 k R t u).comm₁₂

/-- Actual third Koszul cone homology after killing a regular element. -/
def regularH3Equiv (t : R) (u : Fin 3 → R) (ht : Function.Injective (multiply k R t)) :
    (coneShortComplex (threeH3Complex k R u) (multiplyH3 k R t u)
      (threeD2 k R u) (threeD2_comp_threeD3 k R u)).homology ≃ₗ[k]
    (threeH3Complex k (QuotientRing R t) (fun i => quotientAlg k R t (u i))).homology := by
  apply coneQuotientHomologyEquiv (quotientH3 k R t u)
    (threeD2 k R u) (threeD2_comp_threeD3 k R u) (multiplyPi k R t (Fin 3))
  · exact ModuleCat.hom_ext_iff.mp (multiplyH2 k R t u).comm₂₃
  · exact multiplyPi_injective k R t ht (Fin 3)
  · exact multiplyPi_injective k R t ht (Fin 3)
  · exact range_multiply_eq_ker_quotient k R t
  · exact range_multiplyPi_eq_ker_quotientPi k R t (Fin 3)
  · exact quotient_surjective k R t
  · exact quotientPi_surjective k R t (Fin 0)

/-- Degree-three homology with zero incoming differential is the genuine top kernel. -/
def threeH3EquivKer (u : Fin 3 → R) :
    (threeH3Complex k R u).homology ≃ₗ[k] LinearMap.ker (threeD3 k R u) := by
  let S := threeH3Complex k R u
  have hr : LinearMap.range S.moduleCatToCycles = ⊥ := by
    apply LinearMap.range_eq_bot.mpr
    ext x
    rfl
  exact S.moduleCatHomologyIso.toLinearEquiv.trans
    ((LinearMap.range S.moduleCatToCycles).quotEquivOfEqBot hr)

end NSP3.TorSpike.RegularReduction
