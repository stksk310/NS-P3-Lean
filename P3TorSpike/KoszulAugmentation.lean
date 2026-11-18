import P3TorSpike.KoszulComplex
import P3TorSpike.TorObjects

noncomputable section
namespace NSP3.TorSpike.Koszul
open MvPolynomial CategoryTheory
variable {k : Type} [Field k]

theorem remainder_eq_modMonomial (i : Fin 4) (p : PolynomialRing k) :
    remainder i p = p.modMonomial (Finsupp.single i 1) := by
  have h := divMonomial_add_modMonomial_single p i
  dsimp [remainder, quotient]
  exact sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _))

theorem coeff_remainder (i : Fin 4) (p : PolynomialRing k) (d : Fin 4 →₀ ℕ) :
    coeff d (remainder i p) = if d i = 0 then coeff d p else 0 := by
  rw [remainder_eq_modMonomial]
  split_ifs with h
  · apply coeff_modMonomial_of_not_le
    simpa [Finsupp.single_le_iff, h]
  · apply coeff_modMonomial_of_le
    simpa [Finsupp.single_le_iff] using Nat.one_le_iff_ne_zero.mpr h

theorem terminal_remainder (p : PolynomialRing k) :
    remainder 0 (remainder 1 (remainder 2 (remainder 3 p))) = C (constantCoeff p) := by
  ext d
  simp only [coeff_remainder, coeff_C]
  by_cases hd : d = 0
  · subst d; simp [constantCoeff]
  · have hex : ∃ i : Fin 4, d i ≠ 0 := by
      by_contra! h
      exact hd (Finsupp.ext h)
    obtain ⟨i, hi⟩ := hex
    have hd' : (0 : Fin 4 →₀ ℕ) ≠ d := Ne.symm hd
    fin_cases i <;> simp_all

/-- Actual augmentation of the zero-th free Koszul module to the residue field. -/
def augmentation (k : Type) [Field k] :
    ModuleCat.of (PolynomialRing k) (graded k 0) ⟶ residueModule k := by
  letI : Module (PolynomialRing k) k := Module.compHom k MvPolynomial.constantCoeff
  exact ModuleCat.ofHom {
    toFun := fun v => constantCoeff (v.1 0)
    map_add' := by intros; simp
    map_smul' := by
      intro r v
      change constantCoeff (r * v.1 0) = constantCoeff r * constantCoeff (v.1 0)
      exact map_mul _ _ _ }

theorem augmentation_differential (k : Type) [Field k] :
    ModuleCat.ofHom (gradedDifferential k 0) ≫ augmentation k = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change constantCoeff (differential v.1 0) = 0
  simp [differential]

theorem differential_zero_degree (v : graded k 0) : differential v.1 = 0 := by
  have h1 : v.1 1 = 0 := v.2 1 (by decide)
  have h2 : v.1 2 = 0 := v.2 2 (by decide)
  have h3 : v.1 3 = 0 := v.2 3 (by decide)
  have h4 : v.1 4 = 0 := v.2 4 (by decide)
  have h5 : v.1 5 = 0 := v.2 5 (by decide)
  have h6 : v.1 6 = 0 := v.2 6 (by decide)
  have h7 : v.1 7 = 0 := v.2 7 (by decide)
  have h8 : v.1 8 = 0 := v.2 8 (by decide)
  have h9 : v.1 9 = 0 := v.2 9 (by decide)
  have h10 : v.1 10 = 0 := v.2 10 (by decide)
  have h11 : v.1 11 = 0 := v.2 11 (by decide)
  have h12 : v.1 12 = 0 := v.2 12 (by decide)
  have h13 : v.1 13 = 0 := v.2 13 (by decide)
  have h14 : v.1 14 = 0 := v.2 14 (by decide)
  have h15 : v.1 15 = 0 := v.2 15 (by decide)
  funext i
  fin_cases i <;> simp_all [differential]
theorem augmentation_surjective (k : Type) [Field k] :
    Function.Surjective (augmentation k) := by
  intro a
  change k at a
  refine ⟨(gradedEquiv k 0).symm (fun _ => C a), ?_⟩
  change constantCoeff (if degree (0 : Fin 16) = 0 then C a else 0) = a
  simp [degree]

instance augmentation_epi (k : Type) [Field k] : Epi (augmentation k) :=
  (ModuleCat.epi_iff_surjective _).mpr (augmentation_surjective k)

theorem exact_zero (v : graded k 0) (hv : augmentation k v = 0) :
    ∃ w : graded k 1, gradedDifferential k 0 w = v := by
  change constantCoeff (v.1 0) = 0 at hv
  refine ⟨⟨contraction v.1, contraction_mem 0 v⟩, ?_⟩
  apply Subtype.ext
  change differential (contraction v.1) = v.1
  have he : terminalProjection v.1 = 0 := by
    funext i
    fin_cases i <;> simp [terminalProjection, terminal_remainder,
      show constantCoeff (v.1 0) = 0 from hv]
  have h := contraction_identity v.1
  rw [differential_zero_degree v, he] at h
  simpa only [contraction_zero, add_zero, sub_zero] using h

end NSP3.TorSpike.Koszul
